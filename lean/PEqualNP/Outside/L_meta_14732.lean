import PEqualNP.Defs





namespace PEqualNP.Outside.L_meta_14732
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def limbs64 (ws : List Nat) : Nat := ws.foldl (fun v w => (v <<< 64) + w) 0
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

def inputs : List Sig := [(BitVec.ofNat _ (limbs64 [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),(BitVec.ofNat _ (limbs64 [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),(BitVec.ofNat _ (limbs64 [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),(BitVec.ofNat _ (limbs64 [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),(BitVec.ofNat _ (limbs64 [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),(BitVec.ofNat _ (limbs64 [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0x0,0x0]))]
def graph : Sig := (BitVec.ofNat _ (limbs64 [0xfffffffefffffffe,0xfffefffefffefffe,0xfffffffeffffffaa,0xfefefefeeeccaa00,0xfffffffefffffffe,0xfffefffefffefffe,0xfffffffeffffffaa,0xfefefefeeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7)
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
 (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7)
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
  | 0 => (limbs64 [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1])
  | 1 => (limbs64 [0x1,0x0,0x1,0x0,0x1,0x0,0x1])
  | 2 => (limbs64 [0x1,0x1,0x0,0x0,0x1,0x1])
  | 3 => (limbs64 [0x1,0x0,0x0,0x0,0x1])
  | 4 => (limbs64 [0x1,0x1,0x1,0x1])
  | 5 => (limbs64 [0x1,0x0,0x1])
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



def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))

theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior


def mixedPairs (support hints : Nat) : List (Sig × Row × Row) :=
  (selected support).map fun (i, w) =>
    let j := (hints >>> (4 * i)) &&& 15
    let r : Nat := if j < 9 then 1 <<< j else 0
    (w, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| (1 <<< i)))

def mixedColumnOK (m z o q support hints L base : Nat) : Bool :=
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G (vars free) xs && decide (L ≤ count - 1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ base + count))

theorem mixedColumn_sound {m z o q support hints L base : Nat}
    (prior : Lower true (vars q) (graphGoal q) base)
    (ok : mixedColumnOK m z o q support hints L base = true) :
    Slice true (vars m) (graphGoal m) (subcube z o) L := by
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o) == one)) && _) = true at ok
  simp only [Bool.and_eq_true, beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have h := ok.2
  by_cases hq : q = 0
  · simp only [hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lower_count (proper_of _ ok.1.1.1) xs h.1 p bank hr ha)
  · simp only [hq, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lift_ok h.1.2 (proper_of _ ok.1.1.1) (proper_of _ h.1.1) prior p bank hr ha)

theorem mixedBaseZero : Lower true (vars 0) (graphGoal 0) 0 :=
  fun _ _ _ _ => Nat.zero_le _

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


abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
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
 (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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


def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction

theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega


abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
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
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
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
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)



def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2


def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n

theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)

theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2

theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,support,hints,L,base) := s
  ((q == 0 && base == 0) || earlier.contains (q,base)) &&
    ((z == m-q && o == 0 && L == base && zeroSliceOK m q) ||
      mixedColumnOK m z o q support hints L base)

theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  obtain ⟨z,o,q,support,hints,L,base⟩ := s
  simp only [certifiesSlice,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
    List.contains_eq_mem,decide_eq_true_eq] at ok
  have lower : Lower true (vars q) (graphGoal q) base := by
    rcases ok.1 with ⟨rfl,rfl⟩ | he
    · exact mixedBaseZero
    · exact prior (q,base) he
  rcases ok.2 with ⟨⟨⟨rfl,rfl⟩,rfl⟩,h⟩ | h
  · exact zeroSlice_sound h lower
  · exact mixedColumn_sound lower h

theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)

theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)

theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot

def eightInputs := inputs.take 8
def sample8 (r : Row) (j : Fin 8) := bit r (eightInputs.getD j.val zero)
def edge8 (x : Fin 8 → Bool) : Bool :=
 (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7)
theorem edgeTable8 : ∀ r : Row, bit r graph = edge8 (sample8 r) := by decide +kernel
theorem inputList8 : List.ofFn (fun j : Fin 8 => eightInputs.getD j.val zero) = eightInputs := rfl
theorem sampled8 (r : Row) : List.ofFn (sample8 r) = eightInputs.map (bit r) := by
  rw [←inputList8]
  rw [List.map_ofFn]
  rfl

theorem eval8 (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sample8 r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled8]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=edge8 x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eval8 C legal C.output r).trans ((computes (sample8 r)).trans (edgeTable8 r).symm)
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
    rw [←inputList8] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩


def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP137 : Nat → Bits
  | 0 => 0xbfbc
  | 3 => ~~~(0x2130 : Bits)
  | 7 => ~~~(0x108c : Bits)
  | _ => 0

def samplesQ137 : Nat → Bits
  | 0 => 0x4214
  | 3 => 0x280a
  | 7 => ~~~(0xebde : Bits)
  | _ => 0

def compactPerms137 : Array (List Nat) := ([[], [115], [48], [48, 115], [112, 115], [112]] : List (List Nat)).toArray

def compactDomains137 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords137 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount137 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath137 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive137 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords137 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs137 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords137 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords137 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket137 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP201 : Nat → Bits
  | 0 => 0xdffb9cfe776a7b4
  | 3 => ~~~(0x8101c54034a7a0 : Bits)
  | 6 => 0xebdd1b3fcac6f48
  | 7 => ~~~(0x44099b8a40e635c : Bits)
  | _ => 0

def samplesQ201 : Nat → Bits
  | 0 => 0x208041120400224
  | 3 => 0xa0014092000052
  | 6 => 0x1461a064484dd08
  | 7 => ~~~(0xbadef55f6db237e : Bits)
  | _ => 0

def compactPerms201 : Array (List Nat) := ([[], [48], [118], [118, 48]] : List (List Nat)).toArray

def compactDomains201 : Array (Sig × Nat) := ([(subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords201 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount201 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath201 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive201 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords201 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs201 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords201 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords201 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket201 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP141 : Nat → Bits
  | 0 => 0x7afdb87dfe738e3c
  | 2 => 0x6cfad28e3fc43fc0
  | 3 => ~~~(0x220092e0342638f0 : Bits)
  | 7 => ~~~(0x80808100a51860c : Bits)
  | _ => 0

def samplesQ141 : Nat → Bits
  | 0 => 0x521448452029a14
  | 2 => 0x1315c92e0443ff40
  | 3 => 0x228482490901650a
  | 7 => ~~~(0x77bfffef5f7fff5e : Bits)
  | _ => 0

def compactPerms141 : Array (List Nat) := ([[], [48]] : List (List Nat)).toArray

def compactDomains141 : Array (Sig × Nat) := ([(subcube 4 0, 4)] : List (Sig × Nat)).toArray

def compactWords141 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount141 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath141 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive141 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords141 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs141 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords141 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords141 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket141 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP204 : Nat → Bits
  | 2 => 0xebdaf93cbfa437f0
  | 3 => ~~~(0x2010490098243530 : Bits)
  | 6 => 0xbbf750fbfe4b0f8c
  | 7 => ~~~(0x80210c0264b028c : Bits)
  | _ => 0

def samplesQ204 : Nat → Bits
  | 2 => 0x14b424741429a3d0
  | 3 => 0x223008122108a24a
  | 6 => 0x4446a3284a235d84
  | 7 => ~~~(0xf6fd7f767f7da3de : Bits)
  | _ => 0

def compactPerms204 : Array (List Nat) := ([[], [98, 115]] : List (List Nat)).toArray

def compactDomains204 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords204 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount204 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath204 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive204 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords204 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs204 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords204 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords204 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket204 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP205 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xddfefdf,0x7c2dedcff3cffdd8,0xf3937b03cedfcb9b,0xd8e4e793605353b4]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xf8bf7ad,0x9973d00ffffc55a5,0x5dbca44c00f7f40d,0x4fff8808077fec00]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x840208,0x5960ad0060005521,0x7185304fca06890d,0x4ba06d9a27761fa0])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0xee7fafb,0x7fd22a0fff33ff63,0x2ec55c03b1affbfd,0x671855a4a0fc9348]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x4080081,0x3c134ac093000dc0,0xe904f03b5814299,0x445c97a5e059c35c])) : Bits)
  | _ => 0

def samplesQ205 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2209010,0x242122210089801,0x8409008810124888,0x1084010241424224]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x74515a,0x44880f7b42240e73,0xc519d22089f3e401,0x23089a3d55fe400]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x860048,0x11202c0888820630,0x4000404240412242,0x442002114092052]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1182503,0x8004c1d52110214a,0x1930991402ac9110,0x61080c948ab49108]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xbf6fbfe,0xd7eeff7bfbbebef7,0xe7dff7fedbf3efdb,0x77febbebf55fe77e])) : Bits)
  | _ => 0

def compactPerms205 : Array (List Nat) := ([[], [48]] : List (List Nat)).toArray

def compactDomains205 : Array (Sig × Nat) := ([(subcube 4 0, 5), (subcube 64 0, 5), (subcube 0 4, 5), (subcube 1 0, 4), (subcube 8 0, 4), (subcube 128 4, 4)] : List (Sig × Nat)).toArray

def compactWords205 : Nat → Nat
  | 0 => (limbs64 [0x222be51a012f,0x50397e80582b191f])
  | _ => 0

def compactCount205 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0

def compactPath205 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords205 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords205 (83 + 12*i) 12
    (readCompactBits compactWords205 (71 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive205 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords205 (0 + 5*i) 5
  | 5 => readCompactBits compactWords205 (41 + 6*i) 6
  | 4 => readCompactBits compactWords205 (95 + 7*i) 7
  | _ => 0

def compactPoolIDs205 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords205 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords205 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords205 (55 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords205 (47 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords205 (102 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords205 (102 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket205 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords205 (61 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords205 (62 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords205 (104 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords205 (105 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP109 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x4102020c0,0x56c0800008b81f30,0x24703015e4a41641,0x2d68f45ca035ac9a])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x766fadf773,0x5e601fef1ffbd73c,0x1e5a30055ff746d3,0xe9e7c414816cfc88]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x10a0080673,0x214e40041603034e,0x1c1b83ed5140069a,0xd302ccb78fc887e8])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7d9ffe6fdd,0x35ca1fb4fff90fee,0x6cf7816557febed9,0x1f1acc1785b38f88]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x5ebffbbee2,0xe3d4df5ffeb63b53,0xb539f298bdedd72e,0xf76830e82adda472]))
  | _ => 0

def samplesQ109 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x7bedefdfbf,0xed7f7777affbfbaf,0xffebfffe7efdb75d,0xeffbf77beebfeebe])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x9915a2188,0x810ebc2204272472,0x26b6484829774410,0x884108bcf16c7408]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x10a4488212,0x204c524080c24104,0xa482d18406392101,0x2088511940364814]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x26800d220,0x4811431409085104,0xc908921216888048,0x512554106938a80]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2140825105,0x423250122193022,0x4b28042058c49204,0x42200460a689a422]))
  | _ => 0

def compactPerms109 : Array (List Nat) := ([[], [99]] : List (List Nat)).toArray

def compactDomains109 : Array (Sig × Nat) := ([(subcube 4 0, 5), (subcube 0 4, 5), (subcube 8 0, 4), (subcube 64 0, 4), (subcube 32 0, 4), (subcube 32 4, 4)] : List (Sig × Nat)).toArray

def compactWords109 : Nat → Nat
  | 0 => (limbs64 [0x7fa5baaf,0xf7fbfc13f29100bf,0xc3f27bb9c4c07f8f,0xf096f171463ffffe,0x889804805817621f])
  | _ => 0

def compactCount109 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath109 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords109 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords109 (210 + 12*i) 12
    (readCompactBits compactWords109 (198 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive109 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords109 (0 + 5*i) 5
  | 5 => readCompactBits compactWords109 (65 + 6*i) 6
  | 4 => readCompactBits compactWords109 (222 + 7*i) 7
  | _ => 0

def compactPoolIDs109 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords109 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords109 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords109 (91 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords109 (83 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords109 (229 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords109 (229 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket109 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords109 (106 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords109 (110 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords109 (231 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords109 (233 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP233 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x77fffffb75,0x7e7bbff79effcfef,0x83dda7f71dcf3acf,0x2e77ad70bdcd1fb4]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x2080006100,0x663918320004c722,0x801c27f50c091286,0x2036ad40bdcc1fa0])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7a2fe2ff3a,0x639007ffff94f4f1,0xc41e066001fbff70,0x303ff000396fec00]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7ccfbd7cc1,0xe5e41fff796f370e,0x7a3d218cc33ff58f,0xe9ae4ac844fa9348]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x1070201a71,0x61d6b845180034cd,0x421da7eed2022d49,0x282f42f87d8b8f5c])) : Bits)
  | _ => 0

def samplesQ233 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x808000008,0x8080001100880000,0x4000400000c1,0x60200000000624]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2081082000,0x4228140444404004,0x1088050100828828,0x8400409210034052]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x5d20f2895,0xc4fdf4888155167,0x1eec283e27ebe302,0x309b119b19efe800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x334238133,0x1811e18219130c23,0xc62398640f353706,0x19860048c3f89108]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x6f8f5b75ae,0xd6e9d55fd5cee2bf,0x37b8f55b68a3aced,0xad7d76be358bcf7e])) : Bits)
  | _ => 0

def compactPerms233 : Array (List Nat) := ([[], [118]] : List (List Nat)).toArray

def compactDomains233 : Array (Sig × Nat) := ([(subcube 32 0, 5)] : List (Sig × Nat)).toArray

def compactWords233 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount233 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath233 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive233 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords233 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs233 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords233 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords233 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket233 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP173 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xbdfffbe,0xf9276f3e5ffecf87,0xf14fb8799bf3a493,0xefcd1f01f8b9896c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xf57ef5f,0x327ed0bffb97fc7a,0x76b0b28644ffd8fc,0x5e79e01e03c9f690]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x10c0c10,0xb2622d8001067302,0x7700b2fed48210b4,0x6a8cfc1fe3a84ff0])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xdebfff1,0xfed8283fe57ff309,0xff71c076439ff7fc,0x318ee412e0f65990]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x500300,0x781c4a0240108c09,0xf07188774811a4d8,0x1549e712f8d1999c])) : Bits)
  | _ => 0

def samplesQ173 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x4204021,0x4481052020a100c,0x181048040228480,0x8844040309888124]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xa820b1,0x888109706080708e,0x1c1c9101063c814,0x120104131fc9a210]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x10d0494,0x22022da91040a5a2,0x2244c2448259620a,0x42041505655300a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2160506,0x124868c05110530,0xb2161009279c1040,0x210a696460365880]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xfaf7efd,0xafefbdfb77dbffef,0x6fedefddf67bfede,0xbf6fd7dbdfddbbbe])) : Bits)
  | _ => 0

def compactPerms173 : Array (List Nat) := ([[], [82, 112]] : List (List Nat)).toArray

def compactDomains173 : Array (Sig × Nat) := ([(subcube 4 0, 5)] : List (Sig × Nat)).toArray

def compactWords173 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount173 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath173 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive173 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords173 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs173 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords173 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords173 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket173 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP236 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x76fff6fdd73df6,0xd7ff7cdffb5bf315,0xee3c6cd5dfe755e3,0xcfbb730ac6b63fe8]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x10200400c31406,0xd000204c1941c305,0xc40c6cd0888445a2,0xc720730ac6a229e8])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7d8fff8be1ccce,0x87f9e3fff8e1df87,0x3cc00cc7bffcefe5,0xc0e4f1084199eb28]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x5e3fbdf6ea331f,0x7e6bffdc7a5e4ed,0xd138122ff9dfa59a,0x3f7c0c8521ef3114]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x49030802029df,0x80000091e2a1f485,0x38301ee91140a5c1,0x8fc7d8d601d333c])) : Bits)
  | _ => 0

def samplesQ236 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x9014d00208200,0xd01100915441404,0x1282002041e21400,0x8490020c74161548]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x10240c20411004,0x4494021015088524,0x94080105320811,0x806242c141c8612]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x278103c4e2071,0x70e0e482622ac12a,0x4d18b15f961c60c4,0x5160b5b08189ea20]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x21c0c18d1444d0,0xbb204c24ea443093,0x1749e0cef8c1a184,0x730803816be33104]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7b6def6efbf6a4,0x7db5babfb7dd9f66,0xb7bf59b3d5f2dd51,0xaefeefee741fb77e])) : Bits)
  | _ => 0

def compactPerms236 : Array (List Nat) := ([[], [101, 50]] : List (List Nat)).toArray

def compactDomains236 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords236 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def compactCount236 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath236 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive236 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords236 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs236 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords236 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords236 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket236 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP229 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xeffffdfb7757,0xdd7ffdbcfda4ffee,0xfea7f0eeb7ea3b8,0xe3ef9b71dabb4a5e]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x408140831006,0x9d402c001024ba64,0xb4a7f0e0112a310,0x3659b71da920a5e])) : Bits)
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0xb0019005c59,0xc5c1c0004508e0c8,0xccfdc70f002c230c,0xfc889d7d170dc99e])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0xf93f7b9cdc1e,0xa07fff7b550fb249,0xef584300dfbf3f1c,0xde70816012ddac18]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xdebfdfe718e9,0xc5bfeec7fe78e8f4,0xd8f5840fb5ffe347,0x3d8d9c1d05c6d986]))
  | _ => 0

def samplesQ229 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x101102008088,0x2090084481004,0x2804004008482088,0x281024301284052]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0xbf76bdddeffd,0xf6dcffdddf27ed7b,0xd7bfddf7f533efdd,0x6ff7f99cded63b7e])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xb020d084950,0xc4d8528818012942,0x55388d13f111c511,0x53228844ad23220]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x6c465610331,0x5facc4190b944ae3,0x14519936d6b68f01,0x4c6005b02ed5ac08]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x216028482514,0x7254604c4b056121,0x4122c992a5238545,0x2424a91444c61904]))
  | _ => 0

def compactPerms229 : Array (List Nat) := ([[], [117]] : List (List Nat)).toArray

def compactDomains229 : Array (Sig × Nat) := ([(subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords229 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount229 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath229 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive229 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords229 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs229 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords229 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords229 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket229 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP237 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7bbfffef,0xfbfd5f39b7d59efa,0xf7ffdf3e7fff3e7f,0x7f78ffa0ffdcc723,0xdcf4e0571afa1dde,0xc6e79effcfa7f98f,0x633e7ee3df2e36e6,0x3023ef3df4431883,0xe7af4c867ecc0e9b,0xb2722fd8f8a50b93,0x62e619d9a6c53741,0xf59296528a49754]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x6fabfffb,0xf5b7e66bcfa1a999,0x3bfd7ffffbf0d992,0x7bc5ecdf6b7df877,0x2175576be56c7201,0x2107f9f7bfffcf5c,0xfc2dd6bcaef5d7d8,0x8ddd50f44349b75c,0x3204f1118031304c,0xbf7fd73ccf1254e2,0x3da3e53e3cb84804,0xb080d339c9fb6820]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x20840001,0x810816438280943b,0xb0014c0000811c02,0x71812780281c1d63,0xa175457500ba65db,0x65c1004105039181,0x800c962c8b24d70e,0x813de53c6743a314,0xa3a65197fef53ac8,0x94163650543457a3,0x35a2f9e8867d7945,0xbf89fb754915ff60])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7d5cfe37,0xffde9fc6f99a3024,0xe3ffffffce8fbf87,0xcf9f1fc31c1f7fc3,0x1f1f031c6083e189,0x7ffcb7ff871f3,0x83dfbffce7f1c307,0xc07c0fbe1f83e0fc,0x7f000061c31301f,0xdcbff5ef34f9f4e3,0x8d001ee1c7382804,0x17810f4e37139820]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7ee4ffdd,0xbf687fd74e60545f,0xbfffef9b5fd67ee,0xf4a3e37ef4be98e8,0xe060bcf48495ec30,0x10c7f77ffd47bfaf,0x9edb971f19de3c39,0x433cb449a8f4ab30,0xa9abb08061c2813c,0xed9e7af3ff4c5f1d,0x70b9f2e6404291c2,0x40282ef3d1450688]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x8290200,0x30344f004d1138dc,0x6c04123800002386,0x4e00c842541cc2e3,0x5c74b25ee4c5f9bd,0x92e290020824690e,0x21b169004d136f1,0x407c1efd98c1b8f8,0x27a9ac867dfbb520,0xa83a41a8a8c95cd3,0x68a116f764babfc6,0x57f9216bb1e39ebc])) : Bits)
  | _ => 0

def samplesQ237 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x4400410,0x202208208084004,0x12420041014004,0x1100280002040,0x201082804008200,0x1010808401200880,0x228004090042100,0x142044000020410,0x8400021000018000,0x50041808050090,0x2004110022002100,0x1810112008201444]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x10548010,0x4b401104205a5226,0x805808210841e406,0x84d31422a8806480,0x9008808010800118,0x543bd9a481024048,0x100050080280bb28,0xa34304c8480294b0,0x964a084010800900,0x2352553cca024002,0x480840c00806146,0x18f49129c8e92020]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x20841080,0x8908044082001433,0x1240108420082822,0x8090452821080802,0x140041100024550,0x60824c2222140402,0x408020120400984a,0x2409001089108081,0x2c8210440240002,0xa21418682808808,0xa01001050108216,0x244800aa48a0092]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2a320e8,0x9005401904258d59,0x1f842108069008a9,0x1320690d456c082c,0x24847042231c0866,0xa9c4064b3ac0a130,0x8507028061330052,0x448c2314b115490d,0x68a07088874850ff,0xdc29a0c324380541,0x81082a6105198a98,0x23012e4637128800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x11b422a,0x4054c0281096ab80,0xe4a8841882308611,0x456a28c148a1c114,0xc1621406a2c108b,0x8f2d3119cc418015,0xc120704407b4630,0x9220518874897824,0x381314298c4032bc,0xe58e1a6071681700,0xc13860c2000058c1,0x40a36ed151450208]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x77d6f5bd,0xefdbb5f7befedf37,0x92deffb5edebfd67,0xadf7ff3bfbba7dfa,0xbbdbddbb5db2df5a,0xfdbbddafab776def,0xdbbd75deb7cdbbff,0xaf5b8dfbfb73def7,0xbfcebff55badeb42,0xef7b55feead7dadb,0x6eb5dfbf77b6eff6,0x9efdb16bfdebbefe])) : Bits)
  | _ => 0

def compactPerms237 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains237 : Array (Sig × Nat) := ([(subcube 32 0, 7), (subcube 128 0, 7), (subcube 4 0, 6), (subcube 64 0, 6), (subcube 0 4, 6), (subcube 1 0, 5), (subcube 8 0, 5), (subcube 68 0, 5), (subcube 65 0, 4), (subcube 136 0, 4)] : List (Sig × Nat)).toArray

def compactWords237 : Nat → Nat
  | 0 => (limbs64 [0x1800e7042b,0x43fe3fc66dff0ff0,0xf5ff8a0007abd54f,0x97db6f96db888d11,0x27288e659c93380,0xe72602201222200a,0x2201201400a0120,0x8622017f83fc00f,0x62d521414587ab59,0x72f10930ad39497f,0x83fc1fe0dacaf1cc,0xa3fe0e037f80182d,0xa96617f83fc1fe0d,0x17c1a326ee4d2da0,0xd83fc0c35492ab0f,0xfc000001600450a1,0x428cc99364c582f5,0xc396ac18334e6881,0x1183440a0146318c,0x63f992537cbf2b4a,0xd2dfdff7dff7fddf,0xdffdfdff7f5ff7d7,0xdff7cfd7dbfefefe,0xfefefec26026603e,0x223a611a22322232,0x6232601622122216,0x212021662166216,0x6212621062026282,0x620261ac012a010e,0x220a220c010a0162,0x2602401400a22202,0x2012008017f857b8,0x387f87f87f87f83f,0xa712efc67ca50c59,0x1bb4a1a02ccc9872,0xea58ca893f25a863,0x66002048b74ec2c,0x84b56e20d56846a,0x20c85747020d4497,0xa260a4956c20846,0xad566214c4970a96,0xaf4450b749ffffff,0xfffffffff7ee2222,0x2602202601401201,0x1400a00d0e223f])
  | _ => 0

def compactCount237 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 10
  | 6 => 26
  | 5 => 7
  | _ => 0

def compactPath237 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords237 (27 + 12*i) 12
  | 6 => let v := readCompactBits compactWords237 (967 + 16*i) 16
    (readCompactBits compactWords237 (859 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords237 (2547 + 15*i) 15
    (readCompactBits compactWords237 (2403 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive237 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords237 (0 + 6*i) 6
  | 7 => readCompactBits compactWords237 (147 + 7*i) 7
  | 6 => readCompactBits compactWords237 (1383 + 8*i) 8
  | 5 => readCompactBits compactWords237 (2652 + 9*i) 9
  | _ => 0

def compactPoolIDs237 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords237 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords237 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 7 => let v := readCompactBits compactWords237 (557 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords237 (217 + 4*(v &&& 127)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords237 (1691 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits compactWords237 (1591 + 5*(v &&& 31)) (5*n)
    compactIDsFromBits bits 5 n
  | 5 => let v := readCompactBits compactWords237 (2715 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords237 (2715 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket237 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords237 (667 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 15)
    let v := readCompactBits compactWords237 (679 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 6 => let d := readCompactBits compactWords237 (1873 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 38)
    let v := readCompactBits compactWords237 (1909 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords237 (2729 + 1*(i % 3)) 1
    let off := ((i/3 + d) % 11)
    let v := readCompactBits compactWords237 (2732 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x694ffec3e818ea93,0x4df509eb8afd7764,0xb82a87bd94da63ad,0xfc89cadd85e3faae,0xe7842a8139fd1fc9,0x4502a2ae37715006,0xf696208ea62165a8,0x70b0ad6755a65470,0x41891ff4421804eb,0xa6f15e8ced6a98d4,0xbae962439ec3f6e,0xd06b2e1a6b4862e0,0x60177587299e085c,0xc29c44720f50c9ab,0x88085e6312326702,0xd6161548c8c22d54]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xbfefdbfeba65afbb,0xb2bef6124fe8baff,0x41ab949f7b29b512,0x485e3da7ca4375bb,0x7840f18dea72e026,0x8ed1c45298e28c7,0x903dd67007c2335f,0x8703463208872f81,0x8c70600000e13814,0x10edbbcf363291ff,0xed3de9b7ee4db43b,0x662e43ed84228872,0x85183a589a805fa2,0xe85fb239726f0204,0x1086a18000cca5b6,0xe3c2e11e7234d020]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x77fce9dc3cfb5f4d,0xc51c3a3cd7862d7f,0xde37f8e1d8f45ed7,0x8f27416a07bc69f5,0x8482ac1a84744218,0xf1f7c1384a2711a8,0xbc02503d82e8d34,0x43bd38dc22f89b34,0x320280608d124309,0x4dde8dfdd7c9e666,0xcafb41d26395c5b0,0xea9dbab6f0ad3502,0x38a0c01d657ba613,0x139c134f0c094d3,0x271100466105dd38,0x8485aacdd20009f]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xabbdf56fd79ce56c,0xb7e9cdf4297ba718,0xa7e97f430fe79aaf,0xf3f16bb679dd84e6,0x1b790774418a9d29,0x3a008291c489cf51,0x5695a0e79d100c0,0xcf092808559a04a,0x4000b30048000,0xeefefffe9e7f53,0x7f92dfcdaaf7daad,0xbd65d8d96310551d,0x5f4b0de5061df040,0x3c023ac78c202000,0x406000188c07fdf3,0xb0a586438f590200]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xd5f2ffb3ffe71001,0xfa0209fff47fd880,0xbfd407fee0fffd51,0xfffeb407fe01ff59,0x3ffd0007e001ff6,0x80037d4007fea007,0xf8007ff100017a00,0x7f4f4007fa000040,0x1f0138000e018f4,0x7ffdf2fbf51fa8,0x744d27fbd4fa1fd0,0xff91f51b9c8f887f,0x801c85fad000005f,0x3e07f880f8f010c,0x806f8010075adf,0x54f818b320663020]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xde57377f8582baf6,0x7a5ff7473395cd9b,0x565c6836e70ca968,0x30d7f77831fe8b17,0xfc3b0cf3008fe010,0xbe183ecb984097b8,0x679b89015f1c92e7,0xa84e81a9dd207b8a,0x40068c0ff206c200,0x4a33e73f18ade93b,0x91457c69d712635f,0x9fa6fe413d2ea8d,0x3ae47a204ee457a9,0x16c1898480303420,0xe871003d8d11824d,0x8f2fea15028d0e88]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xfebb0ebd437f55fe,0xde3f689fc0252e7,0x69d7fb483f1346fe,0x7289ed9fe3e1648,0xfe04536e970120c7,0x47fc4136f0106e78,0x86680fca0fecc1b,0x90007f58225fc485,0xbe0960100d092502,0xb19f7373ed57668d,0xb6f2ba1e1d2be8c7,0x17d695640c751780,0xc7e38202b163a9a4,0xfd26044b71904a50,0x170e900062ea3aed,0x291125e03598c143]))
  | _ => 0

def samplesQ253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x908124128000020,0x8514014109000000,0x1022831408008029,0x8400000581a00402,0x6000280053000000,0xc0b802081401081,0x130000001014410,0x2002950480010004,0xc00100430001e00,0x4a01284000a0010,0x8260404004c080a,0x4041020803480060,0x200b3000021a0008,0xc00200300d000180,0x8000702280282102,0xd204014048002844]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x220992008a2882a1,0x8184905043000232,0x20081071848800a,0xc1425000c0c93500,0x30504ca24b26282a,0x585988b400420a82,0x2024092412415111,0x4126811621324220,0xa400120650460c0a,0x45a09acd04029046,0xa9340920ce48043a,0x622e42e001220030,0x81918498a08c302,0x600f001124440300,0x88b230c6448ca522,0xe242e10e52044020]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x30844808507a0b00,0x1088300800242960,0x691208200d00480,0x5307406050586820,0x104a448a00922648,0x4220441c00804820,0x8088151088041004,0x48100a0260a80149,0x8120882a04ca0048,0x1488c6995004464,0x4218409060110500,0xaa8888b2a0042414,0x1880091d60018610,0x21181100e0028441,0x29004504185d430,0x48528894200092]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x9a5a44f4caa1728,0xb3c71868816a1d20,0x388e9860b60969c,0xf182c9a0f0c82ca0,0x33962048b4a90a05,0x26424989818d732b,0x4159842693a0040d,0x396816008c93024a,0x847b90661d432ce8,0x7ecdefff6187811,0x7382cf4d2ab598a4,0x8445d808e100153d,0xd091d8b420c8210,0x752a325ea42480d8,0x104241388727fdb3,0xb08506438f510000]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x944069924186110e,0x520304ae94299980,0xc8802cc8c1031d94,0x1880a0b216008a69,0x489804424104545,0xa024044114350010,0xd4c232102894a820,0x941948e85c08a58a,0x4235a0b08710a164,0x385f6532fbe10fa8,0x140902d3108213c0,0x1d902111ac800d87,0x14481a250200075,0x5e0528a82832c0d,0x2340870010135add,0x4b818b120621000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xc252013080042056,0x440004914009,0x4040002080062940,0x1026100400005d,0x840092310804c022,0x111020006c128040,0x2406288100522ba0,0x40440b803007090,0x1200618002008014,0xa813210008a5810a,0x8041302085006251,0x12224441880ca80,0x240c00014e010a0,0x280888000002224,0x682900843050024c,0xd22a814008c0608]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x443204a40085500e,0xa230620a4091004,0x60041800a5025914,0xa8a0980c060049,0xd05121580098100,0x810421407828a158,0x1001828320228288,0x8041004012009402,0x29124810320e025,0x2817611268542281,0x4c0b00a1122e005,0x1010150408910981,0xc160828211202820,0xca0068a10110830,0x5109820822420acd,0x911042021988101]))
  | _ => 0

def compactPerms253 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains253 : Array (Sig × Nat) := ([(subcube 16 0, 9)] : List (Sig × Nat)).toArray

def compactWords253 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount253 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath253 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive253 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords253 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs253 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords253 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords253 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket253 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP218 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x767ff3f78e,0x7e38ffbfdf2fdd0f,0xc1f938c14fbf9873,0x3bdc071e63dd852c]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x20c01180a0,0x729a8108050c6885,0xc8d93af10904da51,0x2d02171feb460fac])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7dafffcd69,0xe3b2ff79bfde7acd,0xb8c5f2b03f7df64b,0xe7321619c9137ea8]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7adfddfef3,0x74c37fdee7f061f1,0xfefe033a7fcedfbc,0x3c6398218dee4ad0]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x103040444b,0x6423821082325149,0xb0e433ba0608942a,0x32739e39cd9942f8])) : Bits)
  | _ => 0

def samplesQ218 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x982248850,0x80861a810104080a,0x1a4e4208838b1821,0x282884a61c9800c]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x20c114a020,0x520a501410852021,0x1269682026a10500,0x9018c44b0491e042]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x254107082,0x84960202603a071,0xc02101053c30a042,0x420670184127620]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x52862080c,0x1148c48c0104b0e,0x90604c0414e020c,0x28421820736c0890]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x6fcf3daffe,0xdbde5afdf7ad3cab,0x3effefeda7abbf6f,0xbefbccdf6dd9e2fe])) : Bits)
  | _ => 0

def compactPerms218 : Array (List Nat) := ([[], [99, 116], [49, 100], [49, 67, 116, 118], [65, 118], [65, 115, 100, 118], [97, 99, 100, 118], [97, 115], [113, 67], [113, 99, 116, 118]] : List (List Nat)).toArray

def compactDomains218 : Array (Sig × Nat) := ([(subcube 2 0, 4), (subcube 8 0, 4), (subcube 16 0, 4), (subcube 64 0, 4), (subcube 128 0, 4)] : List (Sig × Nat)).toArray

def compactWords218 : Nat → Nat
  | 0 => (limbs64 [0xff06f4ff03a,0x6ff0ff05597b2678,0x89f9488020496796,0x446b4db903b47f80,0x59dfe0ff0164cf05,0xfe09d27f83fc066d,0x3ffd00900688d11f])
  | _ => 0

def compactCount218 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath218 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords218 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords218 (297 + 12*i) 12
    (readCompactBits compactWords218 (285 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive218 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords218 (0 + 5*i) 5
  | 5 => readCompactBits compactWords218 (50 + 6*i) 6
  | 4 => readCompactBits compactWords218 (309 + 7*i) 7
  | _ => 0

def compactPoolIDs218 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords218 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords218 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords218 (65 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords218 (62 + 3*(v &&& 1)) (3*n)
    compactIDsFromBits bits 3 n
  | 4 => let v := readCompactBits compactWords218 (316 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords218 (316 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket218 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords218 (69 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 16)
    let v := readCompactBits compactWords218 (77 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords218 (318 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 9)
    let v := readCompactBits compactWords218 (320 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP219 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xfdcffe3fff9a7fd,0x57b57d942bfbf7f7,0xf3edefd73e7864fd,0x57afd30376231f26,0xd93f45b80ff7defd,0x36fe17a72ff99ff9,0x417ca8e2ec0766c8,0xd7cb3129e110f061,0xe2fdfe1af1d77660,0xfaa3ca2951c6b044,0x4253134973634c4]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xbfd3fffcbefd9c7,0x6ba0859b37ffcbbf,0xff7e781c3f9f973f,0xfbd87c19863cee98,0x79c018013efff97f,0xc79ffdf7d30e19fe,0x7f8fc70790383900,0xe8fcc1d0ce630008,0x130ff7dfbee84381,0x3d0e0fbf9e000389,0xf8c04f7ae0174118]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x904000430684d0,0x38137cd28014112,0x9691837160130,0x15040645261dbe14,0xed76599d84010065,0x84a89002374a08dd,0x3179f2b0e6147d04,0xf2f8c1d0cf7bdd28,0xc31dd088c50be7c9,0xb90686ec41628b8d,0xfff77b27143ffd98])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xeeaff5fff96f5b6,0xb75a66468bffff7e,0x6efb772af1d76bfa,0x377662d4699b8d55,0x64f00005bdef77fe,0xbd799b4efecf65c5,0xb86b569c63349e34,0x32f30ce6cc4a0d00,0x2ffec5bd6dbeab59,0xa24db47468200b09,0x939209455fcd8910]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xdf77ffd77f75e78,0xdbc13be9d7fdffdf,0xbf83effbff6f9f42,0xbc0f84e68edcb08e,0x873c8196ff9bafff,0xcea3e65a37f7fe42,0x857070f05fc7f9b7,0xe334c691010ccf12,0x7f1b7be2cf1bf5be,0x4d5285c0a1388c02,0x7369e8f083aba20]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x4c004100815124,0x53306d9294008204,0x220266023849064a,0x320a7092ceba8d8e,0x51b985b7c882001a,0x613074602851562,0xcd6e44c65927bab0,0xe3f704a1ed4eef53,0x620a6712289e7330,0x6e4b8d31b8bcbf4b,0x97b69d5ccb16bb74])) : Bits)
  | _ => 0

def samplesQ219 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x23049404021802,0x488061c4520410,0x3011803301080380,0x6840280400c0a048,0x2000aa00c09410ad,0x42100504018044,0x440320154c00a080,0x340009b810600102,0x2229821801c30020,0x8801402810060048,0x1c14212485142084]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x402e00495100428,0x841e3244c8384288,0x4015134352622990,0x290042a051000004,0x840ac6548e9af006,0x4014080003021088,0x14098207442d4095,0x511156ba41081244,0x973ca3ae04180,0x34040812002a1450,0xb8c41f38e0120018]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x90500051448010,0x281330c21202005,0x84042485a12a014,0x401004024140a10,0x26111c2a484410,0x2201418080a04028,0x1240104020811051,0x409550424a008820,0x882254430301014,0x28021010c891210,0xa20084506a800242]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x115019040e80240,0x482189a935c18820,0x80e8380919920d,0x4443850180205002,0x301398a706406f8,0x120020a180c0124,0x4af2305029c0bb48,0x24cc094000142088,0x6fe68415411c0a01,0x8804060854388,0x711a0451fc58100]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x208820188102085,0x201644120a0c0042,0x30e110400e00840,0x1128501800010121,0x484044610503a900,0xc80845000400601,0x8108ca0a903c4004,0xb00060120830000,0x901058a28e002408,0x4052048080208c06,0xc85a8a002a1820]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xfb3f7fef75ebeff,0xeedfb36ded7feeff,0x7bd5d7fbff7eefb6,0xefd57ffdf5f5fb7f,0xef6eff5ceedef4bf,0x6ff7dfdf9fefd7fe,0x764fb7f76eaff4f7,0xf5b7fffefbffbbee,0xeaabf7de3bff7fbd,0xfedfedfbfcff3679,0xfef6bf7cef96bbfe])) : Bits)
  | _ => 0

def compactPerms219 : Array (List Nat) := ([[], [48], [65, 118], [65, 48, 118]] : List (List Nat)).toArray

def compactDomains219 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 8 0, 7), (subcube 16 0, 7), (subcube 64 0, 7), (subcube 128 0, 7), (subcube 0 2, 6), (subcube 0 16, 6), (subcube 18 0, 5), (subcube 80 0, 5), (subcube 130 0, 5), (subcube 2 16, 5), (subcube 64 16, 5), (subcube 128 2, 5), (subcube 3 0, 4), (subcube 9 0, 4), (subcube 10 0, 4), (subcube 65 0, 4), (subcube 72 0, 4), (subcube 129 0, 4), (subcube 136 0, 4), (subcube 66 16, 4)] : List (Sig × Nat)).toArray

def compactWords219 : Nat → Nat
  | 0 => (limbs64 [0x43db5ff01fe03fc0,0x524f6b6ce350217c,0xa073b00159acd298,0x196c3f48083c78bd,0xfff018c2fea27f80,0xff01fe03fc053bac,0xe53fe01053e73413,0x7344072115b04b89,0x742bfc07f802c7e,0x16ed2103b57f19df,0x18cb2cb09d1c2691,0xb418ff80ff019b2,0xbfc03f4d31421cc1,0x41e9182481080018,0x42010a044c30,0x4000400352082255,0x5cfacd34a5451441,0x434beabc53743352,0xe2abb28a269a52a2,0xc1ee18b15c9118fb,0x8c10b585d80040a0,0xb300b1188706083,0x10058893305800d,0x88c212d0f0c88c5e,0xc820536016142218,0x51b061c106020161,0x1226c9980a6d8112,0x61c18602b0111083,0x90230016470a0c3,0x86026002c223c898,0x24087190c5c0950a,0x1160f581c4995818,0x7951e01991086812,0xe0a0a2ae341c1860,0x23c02c1e69611241,0xd051e1c1910c049,0x2c0c20dac1c18b90,0x218722061c08d0c,0x96801cb2282081c,0x1981a0070659ff7f,0xff6fdfffff7fff7f,0xdf7ffffffffffffd,0x7fff7fffffff7f7f,0x330266044c079869,0x215222a425598a93,0x15262a4445984930,0x9260948528c85090,0xa021cc429885310a,0x1194c10888331066,0x1242a12202201200,0x842cbc3067266428,0x165ea02ff07f83fc,0x14ce2d9cfc739a3d,0x7baaf86e3c7fe0ff,0x70d1e7ceddd8722,0x737a3b801c623040,0x526336bb1bb06176,0x49c60c36d5314e31,0x183bcb317044806e,0x196418a438cc1deb,0x3703c4521c7b169b,0x95e0060fffffffff,0xfffd215191091011,0x8d0090070b1a23f])
  | 1 => (limbs64 [0xff00ae79ff00986c,0xbc25f50a086adc13,0x2f057c07c9666819,0xff000b21692aff00,0xf275ff00c94bff00,0x1c17160b7c332847,0x72033123544f5c1d,0xcc7a453fef2b8262,0xc11fef2e1a7fa440,0xa382e5360a7bff00,0xff00bf6eff00511b,0x6c43ff00596d022f,0xc504527e7a787632,0x83684e7793347e6b,0x376f654af373b906,0x7883f469b75fe202,0x5f458763ff00a809,0xc4460f01ea44e24d,0x49646b527d35f00d,0xa55eff00ff00ed72,0x8c4cff00734e650f,0xff00ff00ff00cb42,0x6d3b955b13489827,0x38088215e656e676,0x7249ff00ff00f157,0x5300cc5a3167ff00,0xda2cff004039b141,0xa6655d80823405c2,0x2001020c10070cb0,0xb0550400d810001,0xd805858d45454545,0x4d050cc4c4cc848c,0x4c040bcb838b4b0a,0xf14150c880808848,0x210000800011,0xe1210440808ba2c1,0x1600801140416100,0x67f7bb7fbb9f3fbd,0xdfa7fbb9deef7d6f,0xb7ebe7f3fbbfbbf5,0x7ebf7aa7fafd7cfe,0x7f5fbf4fe7eb4e23,0xe711b388d9c04485,0x82712b38959c0ace,0x256712b38941c4ac,0xe01e728d395a90ad,0x4e52e730738c090a,0x445067281394088,0x8f4e57a122521539,0xca94e546728b381c,0x9c4c4e4cc5404cc4,0x402cc4401cc2404c,0xc2401cc04854c540,0x44c44024c14024c0,0x4854854044854024,0x4540444440444440,0x142440240440284c,0x4c619fb3dba3e112,0x3f5479b9a17c8bc1,0xf267dc0853c60664,0xae7e5acdb9187875,0xa0c2f8454836f71f,0xac6bfc6276732c82,0xa97f801c2ba13394])
  | 2 => (limbs64 [0xd1329a591f4f3,0xcc1ff82544747359,0x7f837d4bceff05fa,0xf78bee8ff03f93fc,0x702b0cebcabaaea,0x8fb0e25214d05141,0x6d00ce04c54044e5,0x4c44024454044024,0x444044026a53ff00,0xd4376d2d9574ff00])
  | _ => 0

def compactCount219 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 7
  | 7 => 26
  | 6 => 33
  | 5 => 5
  | _ => 0

def compactPath219 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords219 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords219 (955 + 15*i) 15
    (readCompactBits compactWords219 (895 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords219 (4964 + 17*i) 17
    (readCompactBits compactWords219 (4556 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords219 (8432 + 14*i) 14
    (readCompactBits compactWords219 (8288 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive219 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords219 (0 + 6*i) 6
  | 8 => readCompactBits compactWords219 (114 + 7*i) 7
  | 7 => readCompactBits compactWords219 (1345 + 8*i) 8
  | 6 => readCompactBits compactWords219 (5525 + 9*i) 9
  | 5 => readCompactBits compactWords219 (8502 + 10*i) 10
  | _ => 0

def compactPoolIDs219 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords219 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords219 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords219 (543 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords219 (163 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords219 (2771 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords219 (1553 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords219 (5998 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits compactWords219 (5822 + 8*(v &&& 31)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords219 (8553 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords219 (8552 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket219 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords219 (620 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 20)
    let v := readCompactBits compactWords219 (635 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords219 (3083 + 7*(i % 24)) 7
    let off := ((i/24 + d) % 87)
    let v := readCompactBits compactWords219 (3251 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords219 (6262 + 6*(i % 31)) 6
    let off := ((i/31 + d) % 115)
    let v := readCompactBits compactWords219 (6448 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 5 => let d := readCompactBits compactWords219 (8563 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 19)
    let v := readCompactBits compactWords219 (8573 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def samplesP251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x3c71fbe8ffd63ffd,0x67eff026dfe63885,0x40cdf37e541e5fe6,0x9e400f2ff2aab15d,0xb7fa487887dfbfe8,0x6108a27fbb825943,0x322b6cda00a1eb7f,0x39a1000c5ed8d68a,0x9004bd42dc0c6880,0xff017000fc1c6879,0x6434243979e285ef,0x41ecff0272fb6819,0x9603402bf994079f,0x40b11a28647c4069,0xe010221d1269e900,0x674894869c6994c4]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xdeff673ca6f8b0b7,0x8bfd7ff7f9ffe698,0x67f64e8f8a7d90ff,0x70ca6b96fd110fba,0x10a7fe15ba49fa71,0xd23f5e91e48c06b8,0x81d598234d4603cd,0xc20686ef21ff1834,0xe7f1201e070903f,0x5f102e5d48e,0x6b8ff53b73affd5,0x99956a4cd82406e8,0x3c454d11a227c08,0xecec7083bae00f84,0x3e08de22c02005b,0xcd16e03307726118]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xfbdfabffeb37edea,0x7c70ecddf5fec72f,0xfd7a831766a1f305,0x97df99f88eced8e2,0xcce9146f5b3fc280,0x98785980f035939c,0xe41b5530aada7c02,0xdd91d10b6000ecb,0xf3c808ff05030140,0xc36e20e110f8f65,0xebc3182e7614fa8f,0xab1f0ed57f9b9096,0xe8019d06035fe2ec,0x304699943388b052,0xec1f100000841e31,0x1930fb44e3000267]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xffefdfe7f4ffee7e,0xff935f2f379b3b75,0x3ab2bff92946abfc,0x89a1fed70277becd,0x6d14dfb764319d17,0x5c344674c4aaaa1,0xc3086c5d0459484,0xd87ee203491b2781,0x6c0b493cd2e08604,0xc808c00047bbfc,0xb5cfc4fac9f56516,0xf7f33deaed972701,0x6a7aa259e5086b70,0x83c8047fd0030080,0x10c0cc20c9103ed6,0x688b468ce8d40910]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfd7e94d359ef5f37,0xf3feffdfeffddd62,0xe7090df0f59b6cfb,0xef34646effec4ff7,0xeaa7a1d5bda8658e,0x2c34a1161b710d46,0x41ee63034db803ca,0x240686e081e4e140,0xe70e48138006038,0x30000501e28fffff,0xdcbffb97b6cdfa32,0x646aa5b1a778d6f6,0x1b854a4e4c21017,0x1013ef43cd600f05,0x300021c30403ffc,0x22e2197b0b096000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xe7a1fe9f7fa9d7db,0x9defaff8de1bf7fa,0x98cd7cc3bbfa5f19,0x65bf92292d55611d,0x375db7aa47d6480f,0x9ec03268007de003,0x3bc483bcb621f831,0xc758791e0e07a974,0x6182f702228c0740,0xc0f90a04011a7f96,0xbb74dfc40f9f01f9,0xbe2cd0ff02e4b909,0x95fdab220e698502,0xbf1165d40013b008,0x1c005001c334d1af,0x92bd0a3814a49a20]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xff9e7d7f9f5ffbcd,0xfe1f93fb2a65f8df,0x9f37f02cdfe5a402,0x7a7ff5d151bbf622,0xdb5a6bcaf8e63470,0x63878d880782747c,0xde00384c331e0430,0x32a179f1f020503f,0x91b502fc01131883,0x306903a0c2bf7fb,0x5b4b23edc86b1e68,0x5ed3d33f9d404966,0x7c062bdc10b598e1,0x4f2e82280f944032,0x2f21c2048b27ec,0x944525c17092048b]))
  | _ => 0

def samplesQ251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x50028880802811,0x600202600023080,0x4000804210040000,0x4000d0020002040,0x8000003880000818,0x8900044004940,0x810109a04801081,0x100000251208001,0x64a4101009000,0x8000500000000,0x2400041141828401,0x1c0000270202810,0x1400808000282,0xa0000064000064,0x10822311210000,0x6408808284418084]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x59620c2210a011,0x1482a828150a208,0x20400108010,0x4000000448000408,0x1080020412001028,0x21300104d00860,0x93118804cb2120,0x112484445a10212,0x49220a5148080400,0x220400800000000,0x2092112502d1c1,0x98840a4458200448,0x44100112000808,0x44400000422424,0x4a1404a21c208003,0xc510e02206204018]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x920da10648150042,0x40604cc111e00806,0x2450040142004145,0x1110a08082808021,0x4441048201088222,0x180108423110208c,0x20c2004120082940,0x809a8d6400112a92,0x8001201852504050,0x8482148040050a45,0x102182230107884,0xa8180e900c990084,0xa010880041522044,0x2002110512083610,0x6086048880041c11,0x920730443000242]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xdba085e380ee086e,0x613402536021922,0x80323d90c40023e3,0x1f200801398a7,0x22005d8001018790,0x2888c9f85002e504,0x68008453eb201485,0xca8104031018f941,0xd4100328009f8,0xc0680f0e015abec,0x25cc04ea40f50416,0x61533402a5870080,0x6a380050e0c06104,0x302803f880800d3,0xe0c201e10d3e54,0x280b068ce8540100]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfd26144059615520,0xf0b6155044ac4c62,0x8a1a54b0e4c9096b,0xa202b04a942592b3,0x22308cc10da2a083,0x5690051229078488,0x8264e40018208c5e,0x28a331824040c4,0xb4d8350c228502d9,0x1513a8d265efffff,0xc897698092442a32,0x42aa1b1821152a0,0x2c98063464c0b015,0x1503a84d89215381,0x2503404c20407ffc,0x2e2195909082000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2400481036008780,0x198c8308c819c400,0x1a84400008431c00,0xaa002800644110,0x114a04000366001,0x374220100cc1022,0x4212b2000478032,0x24006000aec40000,0x6db0108204030007,0x300108000f8a5410,0x9a30c3040e080148,0x1224c06c0240d001,0x1580220600099400,0x8c1104c000030008,0x1f0030000cc2c1aa,0x9294083010a01820]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6c821831050a528c,0xa80190182a050431,0x8b03509885610822,0x8461019012d1092,0x2a1a884060622100,0x654446a808091002,0xc6044a20d3040008,0x6e210210280c1104,0x1040048600a12089,0x50418b50358af5ba,0x5249204c88290228,0x4601510901405102,0xc8a039420a49020,0x450982488890410a,0x10613044408a23ec,0x1045044130920401]))
  | _ => 0

def compactPerms251 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains251 : Array (Sig × Nat) := ([(subcube 32 0, 10)] : List (Sig × Nat)).toArray

def compactWords251 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount251 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath251 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive251 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords251 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs251 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords251 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords251 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket251 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5c9c009cb62e4c2a,0xd37001c0508802,0xccfa09087800187,0x2e10073779d2722a,0xf93835595d866aa3,0x7d194045024f4b92,0xb2e858a08e964f95,0x227f71de2bb20357,0x422a63b0ab500c83,0x16480188024ce33d,0x70a701f221ae829,0x1b89c00c102cc01e,0x38dc0c405a4f0030,0x4042e3023190e91,0x8f0a81a586742520,0x9520548e0c852944]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x80238f6f11800000,0x37d4003e00a800dd,0xf11000600004e608,0x7685adfd1f9bd,0xce6e196787f300cb,0xcd222eefea921e64,0xa799d43ffe8874f8,0xd230b649e6968c0d,0xe954692a408c7bc0,0x3b434094cb00e85,0x903049f000099950,0x5f6001da49900cd3,0xe519000da1001bc0,0x8039d100dc0010c4,0x421ebd7674cc0ab8,0x400e25026e10c218]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xd14403001440f97,0xdf28814006070320,0x220010038111800,0xd028103fcffa5dfb,0xeffd3fc7eeab3220,0x6d7ffb117ee463ef,0x4a164ec1557be1e1,0x674a14b3d753c171,0x8d57ddcd04c30114,0x40ea721207127c4a,0xa8a6900037e5062d,0x8005ffa3850e6360,0x10e3f00200300400,0x434200c2000061e6,0xcbaf9fe7881b8107,0x44733a21812a0080]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x7248f4c00c17f04d,0xe000748139001400,0x6060346220070,0x24c084bcbe6ddca1,0xfeffe49a2a6cc97c,0xaae523970c9f339,0xa517267e26388eba,0x75a2eaa0e9cc54e6,0x72e28e71f0634e69,0xa80040e1d0018000,0x3d492f8dc98a0780,0x44338e0c0a8d1323,0x47c208b0148e602f,0x8800021026080ef,0x392568462184983a,0xaab052d160000467]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x236300634429b3d0,0xd20a1c00a0600d,0x100584c00486000,0x100202795adcf7f,0x7575e7bd7f699e9c,0xf2c91d847d7f3453,0x1aff21988952b72e,0xadbd8e9d3a6dab2f,0x3da0938ea30c8302,0xaaa7897625ac1332,0xc50181aedc111006,0xbc403003e461bc9d,0x4020030020008180,0xb038100c5086007b,0xb9f331c94e8144d4,0x5903c0f49a401210]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x238f90ea500000,0x37078020005700d2,0xe800803804980f,0xd007505d3e2fa656,0x30d3db7ef7dcf58b,0xb2d48eea95229d88,0xe566ab7f71657347,0xa0f4929cd69708a,0x96896a951c2c743c,0x415bca094b430dba,0x6ac4484000126680,0x409e01d5b6420ccc,0x9a19f00dc1701a00,0x40060ec0a0100039,0x76d562988229f080,0xa2cd8d056186c080]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x86d43006f2e841bd,0xc82c0a80c0007400,0xc007e1c80ea00a0,0x1c0810be0d63fc4,0x9782fee7b050ad77,0x1167b5be831480ed,0x5dc1b9015bed981a,0x98c17576101e3fd0,0x8f7fb44253308097,0x55158ce4b042f0c1,0x5053961235e4d1d3,0x218c1e706ad11000,0x2603b00201e010,0x3880001d018e860a,0x4448de1b71325f47,0x285c802a15413420]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf9887b090993be62,0x82805423f088b20,0xf211812341110750,0xa380aa0633fa3df,0xb8fcab8d9975754,0x8690e1528db9ec16,0x5828d7c6a0870845,0xddd48b4614a1feb8,0x709d14400c93b068,0xbc003716b8bd0044,0x2bc2661ca64287e,0xa27260201132e320,0xaf0404420c80044f,0x741e1020c617914,0xb4f0463819422249,0x17802b589238090b]))
  | _ => 0

def samplesQ255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x288000aa45820200,0x2000040106a80002,0x310208c00801928,0x16634900102a,0x138150104820a80,0x101000500424890,0x2c050a080004191,0x2034101203000206,0x4002618003500d00,0x480088051c6009,0xc00d2000c028,0x1a002000000c405e,0x2800000059010020,0x8006311022880980,0x830a01a186500420,0x500148208050104]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x46322a0604828181,0x2c61a0a190004204,0x433105e0048000c0,0x8162125a4ed01988,0xce2c104684820002,0x4c22042348820a00,0x849014354a804018,0x92103001a4960404,0x6954292040492ac0,0x24140104120a8c,0x9020402020088201,0x452014e249104050,0x2053022409245824,0x1091027c0804c4,0x420c9d26744c0838,0xa240244008018]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x4a048b409086520,0x8a10e0e93220020e,0xc39031f410e00980,0xa9c616fbcfd05dab,0xef3d35c78e810220,0x652852102e4462e4,0xa144c01046ba1a1,0x420204b305504171,0x8c12dc2841430b50,0xaa30200716308a,0x89a2c00470c0860d,0x4900fda048146154,0x60c3400240211010,0x590a20634a4241e6,0xcb2e9de788188107,0x4433322001080080]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x510000112804d001,0x4542295a10420644,0x4802500131244002,0xa042009496614c81,0x7845a0922a640010,0xa0c422850883121,0xa003021e0630042a,0x5402c000e8c85040,0x3060863920014261,0x2022906080001020,0x2d480880c1820304,0x401184888a001701,0x4440283504060106,0x481084280040c06f,0x282528442084901a,0x8a20424160000442]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x2900004940642600,0x82160a4802279cd2,0x6300750316f07,0x200005a59129c633,0x3151e7b96b69189c,0xb0010904351d1013,0x86d21808112b606,0x252c8e8c0a01822b,0x14a0008ba1004100,0xaa0b883201a43130,0xb4081864083000e,0x2812a00184279d84,0xc020480034c005c0,0xa10c009c8083883b,0xb9b320c90a8104c0,0x5901c0f48a400200]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x904d154032601052,0x410c0a0041032c70,0x100a8201c2096213,0x1018e804302fa254,0x10c2ca38715ce109,0x12d488c881200508,0x2122224a31041240,0x809490840293088,0x20102052c245000,0x6c10c80260610430,0x424402c000162090,0x201e001484429480,0x92083151a0522203,0x2040468080100219,0x34d1621800217080,0xa2c4890520824000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2577300101800b8,0x2890a009000121,0x3048016080080080,0x5311c00820962144,0x868208449000a563,0x42b4928200804c,0x5500880058c90800,0x80c1216010062d10,0x830c104058200006,0x5510000420038080,0x8025165004241051,0x188122060d00000,0x303020210ea10,0x1480004114303600,0x4440d61251224b05,0x205c000815003020]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x800804000210004a,0x20401110830,0x14080800c80ba201,0x1410c000200ea254,0x824a2851105444,0x8090214000318402,0x5008814020040844,0x9c0024410208880,0x89004008a08008,0x4c100b0238210050,0x21422400a040810,0xa04a0000144280a0,0x81041040828084c1,0x4c0420400213010,0x14d0421801022240,0x1080091892300801]))
  | _ => 0

def compactPerms255 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains255 : Array (Sig × Nat) := ([(subcube 2 0, 10), (subcube 4 0, 10), (subcube 36 0, 10)] : List (Sig × Nat)).toArray

def compactWords255 : Nat → Nat
  | 0 => 0x312ff
  | _ => 0

def compactCount255 (k : Nat) : Nat := match k with
  | 11 => 1
  | _ => 0

def compactPath255 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => 0
  | _ => 0

def compactLive255 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => readCompactBits compactWords255 (0 + 8*i) 8
  | _ => 0

def compactPoolIDs255 (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let v := readCompactBits compactWords255 (14 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords255 (8 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket255 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid137 : CompactGrid := (137, 3, samplesP137, samplesQ137)
def tab137 : CompactTable := (compactCount137, compactPath137, compactLive137, compactPoolIDs137, compactBucket137)
def check137 (k : Nat) := compactNode grid137 tab137 compactDomains137 compactPerms137 k
def sliceSpecs137 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains137 : ∀ d ∈ compactDomains137, Slice true (vars 137) (graphGoal 137) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs137)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs137 : properPairs (graphGoal 137) (asRow samplesP137) (asRow samplesQ137) :=
  compactPairs (g := grid137) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos137 : ∀ p ∈ compactPerms137, autoOK (graphGoal 137) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c137k3p0 : chartBlock (check137 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev137k3 : chartBlock (check137 3) 0 1 = true :=
  c137k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded137 : Impossible true (graphGoal 137) 3 (vars 137).toFinset := by
  apply compactRoot (g := grid137) (t := tab137) (dom := compactDomains137) (perms := compactPerms137) pairs137 domains137 autos137
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev137k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound137 : Lower true (vars 137) (graphGoal 137) 4 :=
  plain_low (hints := 3) (by decide +kernel) excluded137

def grid201 : CompactGrid := (201, 4, samplesP201, samplesQ201)
def tab201 : CompactTable := (compactCount201, compactPath201, compactLive201, compactPoolIDs201, compactBucket201)
def check201 (k : Nat) := compactNode grid201 tab201 compactDomains201 compactPerms201 k
def sliceSpecs201 : List SliceSpec := [(64, 0, 137, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains201 : ∀ d ∈ compactDomains201, Slice true (vars 201) (graphGoal 201) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(137, 4)]) (specs := sliceSpecs201)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound137
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs201 : properPairs (graphGoal 201) (asRow samplesP201) (asRow samplesQ201) :=
  compactPairs (g := grid201) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos201 : ∀ p ∈ compactPerms201, autoOK (graphGoal 201) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c201k4p0 : chartBlock (check201 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev201k4 : chartBlock (check201 4) 0 1 = true :=
  c201k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded201 : Impossible true (graphGoal 201) 4 (vars 201).toFinset := by
  apply compactRoot (g := grid201) (t := tab201) (dom := compactDomains201) (perms := compactPerms201) pairs201 domains201 autos201
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev201k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound201 : Lower true (vars 201) (graphGoal 201) 5 :=
  plain_low (hints := 3) (by decide +kernel) excluded201

def grid141 : CompactGrid := (141, 4, samplesP141, samplesQ141)
def tab141 : CompactTable := (compactCount141, compactPath141, compactLive141, compactPoolIDs141, compactBucket141)
def check141 (k : Nat) := compactNode grid141 tab141 compactDomains141 compactPerms141 k
def sliceSpecs141 : List SliceSpec := [(4, 0, 137, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains141 : ∀ d ∈ compactDomains141, Slice true (vars 141) (graphGoal 141) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(137, 4)]) (specs := sliceSpecs141)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound137
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs141 : properPairs (graphGoal 141) (asRow samplesP141) (asRow samplesQ141) :=
  compactPairs (g := grid141) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos141 : ∀ p ∈ compactPerms141, autoOK (graphGoal 141) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c141k4p0 : chartBlock (check141 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev141k4 : chartBlock (check141 4) 0 1 = true :=
  c141k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded141 : Impossible true (graphGoal 141) 4 (vars 141).toFinset := by
  apply compactRoot (g := grid141) (t := tab141) (dom := compactDomains141) (perms := compactPerms141) pairs141 domains141 autos141
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev141k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound141 : Lower true (vars 141) (graphGoal 141) 5 :=
  plain_low (hints := 1795) (by decide +kernel) excluded141

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound73 : Lower true (vars 73) (graphGoal 73) 4 :=
  carry_of (old := 73) (rep := 137) (swaps := [118]) (by decide +kernel) bound137

def grid204 : CompactGrid := (204, 3, samplesP204, samplesQ204)
def tab204 : CompactTable := (compactCount204, compactPath204, compactLive204, compactPoolIDs204, compactBucket204)
def check204 (k : Nat) := compactNode grid204 tab204 compactDomains204 compactPerms204 k
def sliceSpecs204 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains204 : ∀ d ∈ compactDomains204, Slice true (vars 204) (graphGoal 204) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs204)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs204 : properPairs (graphGoal 204) (asRow samplesP204) (asRow samplesQ204) :=
  compactPairs (g := grid204) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos204 : ∀ p ∈ compactPerms204, autoOK (graphGoal 204) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c204k3p0 : chartBlock (check204 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev204k3 : chartBlock (check204 3) 0 1 = true :=
  c204k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded204 : Impossible true (graphGoal 204) 3 (vars 204).toFinset := by
  apply compactRoot (g := grid204) (t := tab204) (dom := compactDomains204) (perms := compactPerms204) pairs204 domains204 autos204
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev204k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound204 : Lower true (vars 204) (graphGoal 204) 4 :=
  plain_low (hints := 587228928) (by decide +kernel) excluded204

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound197 : Lower true (vars 197) (graphGoal 197) 4 :=
  carry_of (old := 197) (rep := 204) (swaps := [48]) (by decide +kernel) bound204

def grid205 : CompactGrid := (205, 6, samplesP205, samplesQ205)
def tab205 : CompactTable := (compactCount205, compactPath205, compactLive205, compactPoolIDs205, compactBucket205)
def check205 (k : Nat) := compactNode grid205 tab205 compactDomains205 compactPerms205 k
def sliceSpecs205 : List SliceSpec := [(4, 0, 201, 0, 0, 5, 5), (64, 0, 141, 0, 0, 5, 5), (0, 4, 73, 128, 4026531840, 5, 4), (1, 0, 204, 0, 0, 4, 4), (8, 0, 197, 0, 0, 4, 4), (128, 4, 73, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains205 : ∀ d ∈ compactDomains205, Slice true (vars 205) (graphGoal 205) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(201, 5), (141, 5), (73, 4), (204, 4), (197, 4)]) (specs := sliceSpecs205)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound201
    · exact bound141
    · exact bound73
    · exact bound204
    · exact bound197
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs205 : properPairs (graphGoal 205) (asRow samplesP205) (asRow samplesQ205) :=
  compactPairs (g := grid205) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos205 : ∀ p ∈ compactPerms205, autoOK (graphGoal 205) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c205k4p0 : chartBlock (check205 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev205k4 : chartBlock (check205 4) 0 1 = true :=
  c205k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c205k5p0 : chartBlock (check205 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev205k5 : chartBlock (check205 5) 0 1 = true :=
  c205k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c205k6p0 : chartBlock (check205 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev205k6 : chartBlock (check205 6) 0 1 = true :=
  c205k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded205 : Impossible true (graphGoal 205) 6 (vars 205).toFinset := by
  apply compactRoot (g := grid205) (t := tab205) (dom := compactDomains205) (perms := compactPerms205) pairs205 domains205 autos205
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev205k4
    · exact lev205k5
    · exact lev205k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound205 : Lower true (vars 205) (graphGoal 205) 7 :=
  plain_low (hints := 1795) (by decide +kernel) excluded205

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound105 : Lower true (vars 105) (graphGoal 105) 5 :=
  carry_of (old := 105) (rep := 141) (swaps := [112, 82, 118]) (by decide +kernel) bound141

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound101 : Lower true (vars 101) (graphGoal 101) 4 :=
  carry_of (old := 101) (rep := 204) (swaps := [48, 117]) (by decide +kernel) bound204

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 4 :=
  carry_of (old := 45) (rep := 204) (swaps := [48, 99, 117]) (by decide +kernel) bound204

def grid109 : CompactGrid := (109, 6, samplesP109, samplesQ109)
def tab109 : CompactTable := (compactCount109, compactPath109, compactLive109, compactPoolIDs109, compactBucket109)
def check109 (k : Nat) := compactNode grid109 tab109 compactDomains109 compactPerms109 k
def sliceSpecs109 : List SliceSpec := [(4, 0, 105, 0, 0, 5, 5), (0, 4, 73, 32, 15728640, 5, 4), (8, 0, 101, 0, 0, 4, 4), (64, 0, 45, 0, 0, 4, 4), (32, 0, 73, 0, 0, 4, 4), (32, 4, 73, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains109 : ∀ d ∈ compactDomains109, Slice true (vars 109) (graphGoal 109) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(105, 5), (73, 4), (101, 4), (45, 4)]) (specs := sliceSpecs109)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound105
    · exact bound73
    · exact bound101
    · exact bound45
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs109 : properPairs (graphGoal 109) (asRow samplesP109) (asRow samplesQ109) :=
  compactPairs (g := grid109) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos109 : ∀ p ∈ compactPerms109, autoOK (graphGoal 109) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c109k4p0 : chartBlock (check109 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev109k4 : chartBlock (check109 4) 0 1 = true :=
  c109k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c109k5p0 : chartBlock (check109 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev109k5 : chartBlock (check109 5) 0 3 = true :=
  c109k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c109k6p0 : chartBlock (check109 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev109k6 : chartBlock (check109 6) 0 1 = true :=
  c109k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded109 : Impossible true (graphGoal 109) 6 (vars 109).toFinset := by
  apply compactRoot (g := grid109) (t := tab109) (dom := compactDomains109) (perms := compactPerms109) pairs109 domains109 autos109
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev109k4
    · exact lev109k5
    · exact lev109k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound109 : Lower true (vars 109) (graphGoal 109) 7 :=
  plain_low (hints := 1283) (by decide +kernel) excluded109

def grid233 : CompactGrid := (233, 5, samplesP233, samplesQ233)
def tab233 : CompactTable := (compactCount233, compactPath233, compactLive233, compactPoolIDs233, compactBucket233)
def check233 (k : Nat) := compactNode grid233 tab233 compactDomains233 compactPerms233 k
def sliceSpecs233 : List SliceSpec := [(32, 0, 201, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains233 : ∀ d ∈ compactDomains233, Slice true (vars 233) (graphGoal 233) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(201, 5)]) (specs := sliceSpecs233)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound201
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs233 : properPairs (graphGoal 233) (asRow samplesP233) (asRow samplesQ233) :=
  compactPairs (g := grid233) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos233 : ∀ p ∈ compactPerms233, autoOK (graphGoal 233) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c233k5p0 : chartBlock (check233 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev233k5 : chartBlock (check233 5) 0 1 = true :=
  c233k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded233 : Impossible true (graphGoal 233) 5 (vars 233).toFinset := by
  apply compactRoot (g := grid233) (t := tab233) (dom := compactDomains233) (perms := compactPerms233) pairs233 domains233 autos233
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev233k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound233 : Lower true (vars 233) (graphGoal 233) 6 :=
  plain_low (hints := 3) (by decide +kernel) excluded233

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound169 : Lower true (vars 169) (graphGoal 169) 5 :=
  carry_of (old := 169) (rep := 141) (swaps := [112, 82]) (by decide +kernel) bound141

def grid173 : CompactGrid := (173, 5, samplesP173, samplesQ173)
def tab173 : CompactTable := (compactCount173, compactPath173, compactLive173, compactPoolIDs173, compactBucket173)
def check173 (k : Nat) := compactNode grid173 tab173 compactDomains173 compactPerms173 k
def sliceSpecs173 : List SliceSpec := [(4, 0, 169, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains173 : ∀ d ∈ compactDomains173, Slice true (vars 173) (graphGoal 173) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(169, 5)]) (specs := sliceSpecs173)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound169
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs173 : properPairs (graphGoal 173) (asRow samplesP173) (asRow samplesQ173) :=
  compactPairs (g := grid173) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos173 : ∀ p ∈ compactPerms173, autoOK (graphGoal 173) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c173k5p0 : chartBlock (check173 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev173k5 : chartBlock (check173 5) 0 1 = true :=
  c173k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded173 : Impossible true (graphGoal 173) 5 (vars 173).toFinset := by
  apply compactRoot (g := grid173) (t := tab173) (dom := compactDomains173) (perms := compactPerms173) pairs173 domains173 autos173
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev173k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound173 : Lower true (vars 173) (graphGoal 173) 6 :=
  plain_low (hints := 1283) (by decide +kernel) excluded173

def grid236 : CompactGrid := (236, 4, samplesP236, samplesQ236)
def tab236 : CompactTable := (compactCount236, compactPath236, compactLive236, compactPoolIDs236, compactBucket236)
def check236 (k : Nat) := compactNode grid236 tab236 compactDomains236 compactPerms236 k
def sliceSpecs236 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains236 : ∀ d ∈ compactDomains236, Slice true (vars 236) (graphGoal 236) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs236)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs236 : properPairs (graphGoal 236) (asRow samplesP236) (asRow samplesQ236) :=
  compactPairs (g := grid236) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos236 : ∀ p ∈ compactPerms236, autoOK (graphGoal 236) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c236k4p0 : chartBlock (check236 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev236k4 : chartBlock (check236 4) 0 1 = true :=
  c236k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded236 : Impossible true (graphGoal 236) 4 (vars 236).toFinset := by
  apply compactRoot (g := grid236) (t := tab236) (dom := compactDomains236) (perms := compactPerms236) pairs236 domains236 autos236
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev236k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound236 : Lower true (vars 236) (graphGoal 236) 5 :=
  plain_low (hints := 589325568) (by decide +kernel) excluded236

def grid229 : CompactGrid := (229, 4, samplesP229, samplesQ229)
def tab229 : CompactTable := (compactCount229, compactPath229, compactLive229, compactPoolIDs229, compactBucket229)
def check229 (k : Nat) := compactNode grid229 tab229 compactDomains229 compactPerms229 k
def sliceSpecs229 : List SliceSpec := [(32, 0, 197, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains229 : ∀ d ∈ compactDomains229, Slice true (vars 229) (graphGoal 229) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(197, 4)]) (specs := sliceSpecs229)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound197
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs229 : properPairs (graphGoal 229) (asRow samplesP229) (asRow samplesQ229) :=
  compactPairs (g := grid229) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos229 : ∀ p ∈ compactPerms229, autoOK (graphGoal 229) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c229k4p0 : chartBlock (check229 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev229k4 : chartBlock (check229 4) 0 1 = true :=
  c229k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded229 : Impossible true (graphGoal 229) 4 (vars 229).toFinset := by
  apply compactRoot (g := grid229) (t := tab229) (dom := compactDomains229) (perms := compactPerms229) pairs229 domains229 autos229
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev229k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound229 : Lower true (vars 229) (graphGoal 229) 5 :=
  plain_low (hints := 1285) (by decide +kernel) excluded229

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound172 : Lower true (vars 172) (graphGoal 172) 4 :=
  carry_of (old := 172) (rep := 204) (swaps := [50, 101]) (by decide +kernel) bound204

def grid237 : CompactGrid := (237, 8, samplesP237, samplesQ237)
def tab237 : CompactTable := (compactCount237, compactPath237, compactLive237, compactPoolIDs237, compactBucket237)
def check237 (k : Nat) := compactNode grid237 tab237 compactDomains237 compactPerms237 k
def sliceSpecs237 : List SliceSpec := [(32, 0, 205, 0, 0, 7, 7), (128, 0, 109, 0, 0, 7, 7), (4, 0, 233, 0, 0, 6, 6), (64, 0, 173, 0, 0, 6, 6), (0, 4, 73, 160, 4042260480, 6, 4), (1, 0, 236, 0, 0, 5, 5), (8, 0, 229, 0, 0, 5, 5), (68, 0, 169, 0, 0, 5, 5), (65, 0, 172, 0, 0, 4, 4), (136, 0, 101, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains237 : ∀ d ∈ compactDomains237, Slice true (vars 237) (graphGoal 237) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(205, 7), (109, 7), (233, 6), (173, 6), (73, 4), (236, 5), (229, 5), (169, 5), (172, 4), (101, 4)]) (specs := sliceSpecs237)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound205
    · exact bound109
    · exact bound233
    · exact bound173
    · exact bound73
    · exact bound236
    · exact bound229
    · exact bound169
    · exact bound172
    · exact bound101
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs237 : properPairs (graphGoal 237) (asRow samplesP237) (asRow samplesQ237) :=
  compactPairs (g := grid237) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos237 : ∀ p ∈ compactPerms237, autoOK (graphGoal 237) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k5p0 : chartBlock (check237 5) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k5 : chartBlock (check237 5) 0 7 = true :=
  c237k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k6p0 : chartBlock (check237 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k6p1 : chartBlock (check237 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k6p2 : chartBlock (check237 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k6p3 : chartBlock (check237 6) 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k6 : chartBlock (check237 6) 0 26 = true :=
  (chartBlock_join (a := 16) (b := 10) (chartBlock_join (a := 8) (b := 8) c237k6p0 c237k6p1) (chartBlock_join (a := 8) (b := 2) c237k6p2 c237k6p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k7p0 : chartBlock (check237 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k7p1 : chartBlock (check237 7) 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k7 : chartBlock (check237 7) 0 10 = true :=
  (chartBlock_join (a := 8) (b := 2) c237k7p0 c237k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k8p0 : chartBlock (check237 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k8 : chartBlock (check237 8) 0 1 = true :=
  c237k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded237 : Impossible true (graphGoal 237) 8 (vars 237).toFinset := by
  apply compactRoot (g := grid237) (t := tab237) (dom := compactDomains237) (perms := compactPerms237) pairs237 domains237 autos237
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev237k5
    · exact lev237k6
    · exact lev237k7
    · exact lev237k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound237 : Lower true (vars 237) (graphGoal 237) 9 :=
  plain_low (hints := 1283) (by decide +kernel) excluded237

def grid253 : CompactGrid := (253, 9, samplesP253, samplesQ253)
def tab253 : CompactTable := (compactCount253, compactPath253, compactLive253, compactPoolIDs253, compactBucket253)
def check253 (k : Nat) := compactNode grid253 tab253 compactDomains253 compactPerms253 k
def sliceSpecs253 : List SliceSpec := [(16, 0, 237, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains253 : ∀ d ∈ compactDomains253, Slice true (vars 253) (graphGoal 253) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(237, 9)]) (specs := sliceSpecs253)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound237
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs253 : properPairs (graphGoal 253) (asRow samplesP253) (asRow samplesQ253) :=
  compactPairs (g := grid253) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos253 : ∀ p ∈ compactPerms253, autoOK (graphGoal 253) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c253k9p0 : chartBlock (check253 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev253k9 : chartBlock (check253 9) 0 1 = true :=
  c253k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded253 : Impossible true (graphGoal 253) 9 (vars 253).toFinset := by
  apply compactRoot (g := grid253) (t := tab253) (dom := compactDomains253) (perms := compactPerms253) pairs253 domains253 autos253
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev253k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound253 : Lower true (vars 253) (graphGoal 253) 10 :=
  plain_low (hints := 394499) (by decide +kernel) excluded253

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound216 : Lower true (vars 216) (graphGoal 216) 4 :=
  carry_of (old := 216) (rep := 204) (swaps := [66, 118]) (by decide +kernel) bound204

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound210 : Lower true (vars 210) (graphGoal 210) 4 :=
  carry_of (old := 210) (rep := 204) (swaps := [113, 67, 114]) (by decide +kernel) bound204

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound202 : Lower true (vars 202) (graphGoal 202) 4 :=
  carry_of (old := 202) (rep := 204) (swaps := [33]) (by decide +kernel) bound204

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound154 : Lower true (vars 154) (graphGoal 154) 4 :=
  carry_of (old := 154) (rep := 204) (swaps := [49, 50, 100]) (by decide +kernel) bound204

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound90 : Lower true (vars 90) (graphGoal 90) 4 :=
  carry_of (old := 90) (rep := 204) (swaps := [33, 99, 116]) (by decide +kernel) bound204

def grid218 : CompactGrid := (218, 6, samplesP218, samplesQ218)
def tab218 : CompactTable := (compactCount218, compactPath218, compactLive218, compactPoolIDs218, compactBucket218)
def check218 (k : Nat) := compactNode grid218 tab218 compactDomains218 compactPerms218 k
def sliceSpecs218 : List SliceSpec := [(2, 0, 216, 0, 0, 4, 4), (8, 0, 210, 0, 0, 4, 4), (16, 0, 202, 0, 0, 4, 4), (64, 0, 154, 0, 0, 4, 4), (128, 0, 90, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains218 : ∀ d ∈ compactDomains218, Slice true (vars 218) (graphGoal 218) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(216, 4), (210, 4), (202, 4), (154, 4), (90, 4)]) (specs := sliceSpecs218)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound216
    · exact bound210
    · exact bound202
    · exact bound154
    · exact bound90
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs218 : properPairs (graphGoal 218) (asRow samplesP218) (asRow samplesQ218) :=
  compactPairs (g := grid218) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos218 : ∀ p ∈ compactPerms218, autoOK (graphGoal 218) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c218k4p0 : chartBlock (check218 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev218k4 : chartBlock (check218 4) 0 1 = true :=
  c218k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c218k5p0 : chartBlock (check218 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev218k5 : chartBlock (check218 5) 0 2 = true :=
  c218k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c218k6p0 : chartBlock (check218 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev218k6 : chartBlock (check218 6) 0 1 = true :=
  c218k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded218 : Impossible true (graphGoal 218) 6 (vars 218).toFinset := by
  apply compactRoot (g := grid218) (t := tab218) (dom := compactDomains218) (perms := compactPerms218) pairs218 domains218 autos218
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev218k4
    · exact lev218k5
    · exact lev218k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound218 : Lower true (vars 218) (graphGoal 218) 7 :=
  plain_low (hints := 318857280) (by decide +kernel) excluded218

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound217 : Lower true (vars 217) (graphGoal 217) 7 :=
  carry_of (old := 217) (rep := 205) (swaps := [66, 118]) (by decide +kernel) bound205

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound211 : Lower true (vars 211) (graphGoal 211) 7 :=
  carry_of (old := 211) (rep := 218) (swaps := [48]) (by decide +kernel) bound218

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound203 : Lower true (vars 203) (graphGoal 203) 7 :=
  carry_of (old := 203) (rep := 205) (swaps := [33]) (by decide +kernel) bound205

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound155 : Lower true (vars 155) (graphGoal 155) 7 :=
  carry_of (old := 155) (rep := 109) (swaps := [96, 81, 66, 118, 82]) (by decide +kernel) bound109

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound91 : Lower true (vars 91) (graphGoal 91) 7 :=
  carry_of (old := 91) (rep := 109) (swaps := [96, 33, 84]) (by decide +kernel) bound109

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound139 : Lower true (vars 139) (graphGoal 139) 5 :=
  carry_of (old := 139) (rep := 141) (swaps := [33]) (by decide +kernel) bound141

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound89 : Lower true (vars 89) (graphGoal 89) 5 :=
  carry_of (old := 89) (rep := 141) (swaps := [66, 118]) (by decide +kernel) bound141

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound209 : Lower true (vars 209) (graphGoal 209) 4 :=
  carry_of (old := 209) (rep := 204) (swaps := [48, 66, 118, 50]) (by decide +kernel) bound204

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound147 : Lower true (vars 147) (graphGoal 147) 4 :=
  carry_of (old := 147) (rep := 204) (swaps := [32, 49, 100]) (by decide +kernel) bound204

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound83 : Lower true (vars 83) (graphGoal 83) 4 :=
  carry_of (old := 83) (rep := 204) (swaps := [32, 97, 67, 118, 115]) (by decide +kernel) bound204

def grid219 : CompactGrid := (219, 9, samplesP219, samplesQ219)
def tab219 : CompactTable := (compactCount219, compactPath219, compactLive219, compactPoolIDs219, compactBucket219)
def check219 (k : Nat) := compactNode grid219 tab219 compactDomains219 compactPerms219 k
def sliceSpecs219 : List SliceSpec := [(1, 0, 218, 0, 0, 7, 7), (2, 0, 217, 0, 0, 7, 7), (8, 0, 211, 0, 0, 7, 7), (16, 0, 203, 0, 0, 7, 7), (64, 0, 155, 0, 0, 7, 7), (128, 0, 91, 0, 0, 7, 7), (0, 2, 73, 144, 4027514880, 6, 4), (0, 16, 137, 66, 251658480, 6, 4), (18, 0, 201, 0, 0, 5, 5), (80, 0, 139, 0, 0, 5, 5), (130, 0, 89, 0, 0, 5, 5), (2, 16, 137, 64, 251658240, 5, 4), (64, 16, 137, 2, 240, 5, 4), (128, 2, 73, 16, 983040, 5, 4), (3, 0, 216, 0, 0, 4, 4), (9, 0, 210, 0, 0, 4, 4), (10, 0, 209, 0, 0, 4, 4), (65, 0, 154, 0, 0, 4, 4), (72, 0, 147, 0, 0, 4, 4), (129, 0, 90, 0, 0, 4, 4), (136, 0, 83, 0, 0, 4, 4), (66, 16, 137, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains219 : ∀ d ∈ compactDomains219, Slice true (vars 219) (graphGoal 219) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(218, 7), (217, 7), (211, 7), (203, 7), (155, 7), (91, 7), (73, 4), (137, 4), (201, 5), (139, 5), (89, 5), (216, 4), (210, 4), (209, 4), (154, 4), (147, 4), (90, 4), (83, 4)]) (specs := sliceSpecs219)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound218
    · exact bound217
    · exact bound211
    · exact bound203
    · exact bound155
    · exact bound91
    · exact bound73
    · exact bound137
    · exact bound201
    · exact bound139
    · exact bound89
    · exact bound216
    · exact bound210
    · exact bound209
    · exact bound154
    · exact bound147
    · exact bound90
    · exact bound83
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs219 : properPairs (graphGoal 219) (asRow samplesP219) (asRow samplesQ219) :=
  compactPairs (g := grid219) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos219 : ∀ p ∈ compactPerms219, autoOK (graphGoal 219) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k5p0 : chartBlock (check219 5) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k5 : chartBlock (check219 5) 0 5 = true :=
  c219k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k6p0 : chartBlock (check219 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k6p1 : chartBlock (check219 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k6p2 : chartBlock (check219 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k6p3 : chartBlock (check219 6) 24 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k6p4 : chartBlock (check219 6) 32 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k6 : chartBlock (check219 6) 0 33 = true :=
  (chartBlock_join (a := 16) (b := 17) (chartBlock_join (a := 8) (b := 8) c219k6p0 c219k6p1) (chartBlock_join (a := 8) (b := 9) c219k6p2 (chartBlock_join (a := 8) (b := 1) c219k6p3 c219k6p4)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k7p0 : chartBlock (check219 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k7p1 : chartBlock (check219 7) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k7p2 : chartBlock (check219 7) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k7p3 : chartBlock (check219 7) 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k7 : chartBlock (check219 7) 0 26 = true :=
  (chartBlock_join (a := 16) (b := 10) (chartBlock_join (a := 8) (b := 8) c219k7p0 c219k7p1) (chartBlock_join (a := 8) (b := 2) c219k7p2 c219k7p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k8p0 : chartBlock (check219 8) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k8 : chartBlock (check219 8) 0 7 = true :=
  c219k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k9p0 : chartBlock (check219 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k9 : chartBlock (check219 9) 0 1 = true :=
  c219k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded219 : Impossible true (graphGoal 219) 9 (vars 219).toFinset := by
  apply compactRoot (g := grid219) (t := tab219) (dom := compactDomains219) (perms := compactPerms219) pairs219 domains219 autos219
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev219k5
    · exact lev219k6
    · exact lev219k7
    · exact lev219k8
    · exact lev219k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound219 : Lower true (vars 219) (graphGoal 219) 10 :=
  plain_low (hints := 65603) (by decide +kernel) excluded219

def grid251 : CompactGrid := (251, 9, samplesP251, samplesQ251)
def tab251 : CompactTable := (compactCount251, compactPath251, compactLive251, compactPoolIDs251, compactBucket251)
def check251 (k : Nat) := compactNode grid251 tab251 compactDomains251 compactPerms251 k
def sliceSpecs251 : List SliceSpec := [(32, 0, 219, 0, 0, 10, 10)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains251 : ∀ d ∈ compactDomains251, Slice true (vars 251) (graphGoal 251) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(219, 10)]) (specs := sliceSpecs251)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound219
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs251 : properPairs (graphGoal 251) (asRow samplesP251) (asRow samplesQ251) :=
  compactPairs (g := grid251) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos251 : ∀ p ∈ compactPerms251, autoOK (graphGoal 251) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c251k9p0 : chartBlock (check251 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev251k9 : chartBlock (check251 9) 0 1 = true :=
  c251k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded251 : Impossible true (graphGoal 251) 9 (vars 251).toFinset := by
  apply compactRoot (g := grid251) (t := tab251) (dom := compactDomains251) (perms := compactPerms251) pairs251 domains251 autos251
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev251k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound251 : Lower true (vars 251) (graphGoal 251) 10 :=
  plain_low (hints := 65603) (by decide +kernel) excluded251

def grid255 : CompactGrid := (255, 11, samplesP255, samplesQ255)
def tab255 : CompactTable := (compactCount255, compactPath255, compactLive255, compactPoolIDs255, compactBucket255)
def check255 (k : Nat) := compactNode grid255 tab255 compactDomains255 compactPerms255 k
def sliceSpecs255 : List SliceSpec := [(2, 0, 253, 0, 0, 10, 10), (4, 0, 251, 0, 0, 10, 10), (36, 0, 219, 0, 0, 10, 10)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains255 : ∀ d ∈ compactDomains255, Slice true (vars 255) (graphGoal 255) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(253, 10), (251, 10), (219, 10)]) (specs := sliceSpecs255)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact bound253
    · exact bound251
    · exact bound219
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs255 : properPairs (graphGoal 255) (asRow samplesP255) (asRow samplesQ255) :=
  compactPairs (g := grid255) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos255 : ∀ p ∈ compactPerms255, autoOK (graphGoal 255) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k11p0 : chartBlock (check255 11) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k11 : chartBlock (check255 11) 0 1 = true :=
  c255k11p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded255 : Impossible true (graphGoal 255) 11 (vars 255).toFinset := by
  apply compactRoot (g := grid255) (t := tab255) (dom := compactDomains255) (perms := compactPerms255) pairs255 domains255 autos255
  · intro k hk
    change k ≤ 11 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev255k11
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound255 : Lower true (vars 255) (graphGoal 255) 12 :=
  plain_low (hints := 66883) (by decide +kernel) excluded255
def winningGates : List Gate := [⟨.or,[7,6]⟩, ⟨.or,[7,5]⟩, ⟨.or,[6,3]⟩, ⟨.or,[6,1]⟩, ⟨.or,[2,1]⟩, ⟨.or,[9,10]⟩, ⟨.and,[11,4]⟩, ⟨.and,[9,12]⟩, ⟨.and,[13,0]⟩, ⟨.and,[8,3]⟩, ⟨.or,[17,16]⟩, ⟨.or,[18,15]⟩, ⟨.or,[19,14]⟩]
theorem winningLegal : ∀ g ∈ winningGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [winningGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem winningCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨winningGates,20⟩ (List.ofFn x) = edge8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem asListed : ∀ x : Fin 8 → Bool, edge8 x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_14732

open PEqualNP.Outside.L_meta_14732 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_14732 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ correct
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g,hg,op⟩ := hn
    have lt : gates.countP (fun q => !isNot q) < gates.length := by
      rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
      · exact h
      · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
        simp [isNot,op] at eq
    obtain ⟨k,hk,run⟩ := physicalSigned ⟨gates,o⟩ legal (fun x => (correct x).trans (asListed x).symm)
    change k ≤ gates.countP (fun q => !isNot q) at hk
    have low : 11 < k := by
      by_contra! small
      apply excluded255 k small
      have same : graph = graphGoal 255 := by decide +kernel
      simpa only [←same, show vars 255 = eightInputs by rfl] using run
    exact ⟨winningGates,20,winningLegal,by change 13 ≤ gates.length; omega, fun x => (winningCorrect x).trans (asListed x)⟩
  · refine ⟨gates,o,?_,le_rfl,correct⟩
    intro g hg
    obtain ⟨op,arity⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),arity⟩
