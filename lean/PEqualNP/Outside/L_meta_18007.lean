import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18007.NineInputs

open PEqualNP.CircuitLowerBounds
def readWords (ws : List Nat) : Nat :=
  ws.foldl (fun a b => (a <<< 72) + b) 0

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
def inputs : List Sig := [(readWords [170,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaa]),(readWords [204,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc,0xcccccccccccccccccc]),(readWords [240,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0]),(readWords [255,0xff00ff00ff00ff00,0xff00ff00ff00ff00ff,0xff00ff00ff00ff00,0xff00ff00ff00ff00ff,0xff00ff00ff00ff00,0xff00ff00ff00ff00ff,0xff00ff00ff00ff00]),(readWords [255,0xff0000ffff0000ffff,0xffff0000ffff00,0xffff0000ffff0000,0xffff0000ffff0000ff,0xff0000ffff0000ffff,0xffff0000ffff00,0xffff0000ffff0000]),(readWords [255,0xffffff00000000ffff,0xffff00000000ffffff,0xff00000000ffffffff,0xffffffff00,0xffffffff0000,0xffffffff000000,0xffffffff00000000]),(readWords [255,0xffffffffffffff0000,16777215,0xffffffffff00000000,0xffffffffff,0xffffff000000000000,0xffffffffffffff,0xff0000000000000000]),(readWords [255,0xffffffffffffffffff,0xffffffffffff000000,0,0xffffffffff,0xffffffffffffffffff,0xffff00000000000000,0]),(readWords [255,0xffffffffffffffffff,0xffffffffffffffffff,0xffffffffffffffffff,0xffffffff0000000000,0,0,0])]
def graph : Sig := (readWords [255,0xffffffffffffffffff,0xfffffffafff8ffffff,0xffffffffffffffffff,0xffeaffc8ffffffffff,0xfefcfcfffffffffffa,0xf8f8ffeefeeeffeefc,0xccffeafaeaffeaf8c8])

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r):=by decide +kernel
theorem graph_proper : proper graph:=by unfold proper; decide +kernel

theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def dX : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def dY : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def dZ : Nat → Nat
  | 0 => (readWords [65536,16777216,4294967296,1099511627776,281474976710656,72057594037927936,0x10000000000000001])
  | 1 => (readWords [16777216,0,1099511627776,0,72057594037927936,1])
  | 2 => (readWords [4294967296,1099511627776,0,0,0x10000000000000001])
  | 3 => (readWords [1099511627776,0,0,1])
  | 4 => (readWords [281474976710656,72057594037927936,0x10000000000000001])
  | 5 => (readWords [72057594037927936,1])
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((dX (fixed &&& 7)*dY ((fixed >>> 3) &&& 7)*dZ ((fixed >>> 6) &&& 7)) <<< o)
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
def readField (x off width : Nat) := (x >>> off) % 2^width
def readRows {α : Type} (width : Nat) (read : Nat → α) : Nat → Nat → List α
  | 0, _ => []
  | k+1, x => read x :: readRows width read k (x >>> width)
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
theorem w2 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem w3 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem w4 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem w5 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem w6 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem w7 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem w8 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem w9 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem wA : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact w2 r
  · exact w3 r
  · exact w4 r
  · exact w5 r
  · exact w6 r
  · exact w7 r
  · exact w8 r
  · exact w9 r
  · exact wA r
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
    getPairs data cw d (packedAt data pos 5) (pos+5+marker)
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
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
def witPairs (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((selected m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def fullOK (m : Nat) (rs : List Nat) : Bool :=
  let xs := witPairs m rs
  checkEssential (graphGoal m) (varsX m) xs && (xs.map Prod.fst == vars m) &&
    properB (graphGoal m) && decide (varsX m = vars m ++ [typeWord (m/512-1)])
theorem full_split {u} {m : Nat} {rs : List Nat} (ok : fullOK m rs = true) {k : Nat} {S : Finset Sig}
    (h : Live u (graphGoal m) k S) (sub : ∀ v ∈ S, v ∈ varsX m) :
    S=(vars m).toFinset ∨ S=(varsX m).toFinset := by
  simp only [fullOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (varsX m) v sub r s hd hi
  have mem : ∀ v, v ∈ varsX m ↔ v ∈ vars m ∨ v=typeWord (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : typeWord (m/512-1) ∈ S
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
    · exact absurd hv hs
theorem strong_full {u} {m q cap : Nat} {rs : List Nat} (ok : fullOK m rs = true)
    (e : graphGoal m = graphGoal q) (ev : vars m = vars q)
    (a : Impossible u (graphGoal q) cap (vars q).toFinset)
    (b : Impossible u (graphGoal q) cap (varsX m).toFinset) :
    Lower u (varsX m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [fullOK,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.1.2) (essential_plain ok'.1.1.1).1 (essential_plain ok'.1.1.1).2 hr ha
  by_contra! small
  rcases full_split ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
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
structure FreeRooms (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n
structure SingleFactor (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : KWRooms inner pivot
  outside : FreeRooms outer T pivot
def freeFrom {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect
def freeHide {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩
def factorOfTree {S T} (D : KWRooms S T) : SingleFactor S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl ⟨hp,hn⟩
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }
def freeFork {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreeRooms (insert (bin d a b) U) T h) : FreeRooms (insert a (insert b U)) T h := by
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
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
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
theorem supportSide {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB
def factorExpand {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : SingleFactor (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : KWRooms (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,kwFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreeRooms (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freeFork hd ha hb (by simp [z]) old⟩
def factorKeep {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : KWRooms (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : FreeRooms (insert z (U.erase a)) T a := set0 ▸ freeHide (freeFrom H a)
  have H1 := freeFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreeRooms (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,kwLeaf a,freeHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp
theorem oneShare {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (SingleFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨factorOfTree (kwLeaf T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨factorKeep hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : KWRooms (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := factorKeep hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨factorExpand hd01 fa fb zU F⟩
theorem factorForced {S : Finset Sig} {T : Sig} (F : SingleFactor S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
theorem factorOuterOwn {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a p n} (ao : a∈F.outer)
    (one : onlyWire S T a p n) : F.outside.owns a p n := by
  rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.outside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw
theorem outerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (factorOuterOwn F aout A) (factorOuterOwn F aout C))
    (F.outside.rect (factorOuterOwn F bout B) (factorOuterOwn F bout D)))
theorem innerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (A : onlyWire F.inner F.pivot a p na) (B : onlyWire F.inner F.pivot b p nb)
    (C : onlyWire F.inner F.pivot a pa n) (D : onlyWire F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (kwOwn F.inside A) (kwOwn F.inside C))
    (F.inside.rect (kwOwn F.inside B) (kwOwn F.inside D)))
theorem innerSource {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {v p n}
    (hv : v∈F.inner) (only : onlyWire S T v p n) : onlyWire F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply factorForced F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
theorem hornRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b c p n pa na}
    (ar : onlyWire S T a p na) (br : onlyWire S T b pa n) (cr : onlyWire S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := innerSource F ia ar
  have bh := innerSource F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi
theorem parityRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : onlyWire S T a p na) (h2 : onlyWire S T b p nb)
    (h3 : onlyWire S T a pa n) (h4 : onlyWire S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact innerCannotCross F ne (innerSource F ia h1) (innerSource F ib h2)
      (innerSource F ia h3) (innerSource F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact outerCannotCross F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
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
abbrev PanelTag := Nat × Nat × Nat
def panelClosed (arity : Nat) (tags : List PanelTag) : Prop :=
  ∀ {S T}, (F : SingleFactor S T) → (w : Nat → Sig) → (p n : Nat → Row) →
    (∀ i<arity, w i∈S) → (∀ i<arity, ∀ j<arity, i≠j → w i≠w j) →
    (∀ t∈tags, onlyWire S T (w t.1) (p t.2.1) (n t.2.2)) → False
structure PanelProof where
  arity : Nat
  tags : List PanelTag
  closed : panelClosed arity tags
def u8 : List PanelTag := [(0,0,2),(1,1,2),(2,2,3),(3,3,3),(0,4,1),(1,4,3),(2,5,0),(3,5,1),(3,5,2)]
theorem wP (A0 A1 A2 A3 : Prop) : (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A2 → A1) → (A0 → A3 → A1) → (A2 → A1 → A3) → False := by tauto
theorem k5 : panelClosed 4 u8 := by
  intro S T F w p n mem diff cells
  have c0 := cells (0,0,2) (by decide)
  have c1 := cells (1,1,2) (by decide)
  have c2 := cells (2,2,3) (by decide)
  have c3 := cells (3,3,3) (by decide)
  have c4 := cells (0,4,1) (by decide)
  have c5 := cells (1,4,3) (by decide)
  have c6 := cells (2,5,0) (by decide)
  have c7 := cells (3,5,1) (by decide)
  have c8 := cells (3,5,2) (by decide)
  have r0 := parityRule F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
  have r1 := parityRule F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
  have r2 := hornRule F c5 c7 c4
  have r3 := hornRule F c4 c2 c5
  have r4 := hornRule F c4 c3 c5
  have r5 := hornRule F c6 c1 c8
  exact wP (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def u9 : List PanelTag := [(0,0,1),(1,1,3),(2,2,0),(1,2,2),(3,3,1),(2,3,3),(3,4,2),(0,4,3)]
theorem wQ (A0 A1 A2 A3 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A3 → A1) → (A2 → A0 → A3) → (A3 → A1 → A2) → (A0 → A1 → A3) → False := by tauto
theorem k6 : panelClosed 4 u9 := by
  intro S T F w p n mem diff cells
  have c0 := cells (0,0,1) (by decide)
  have c1 := cells (1,1,3) (by decide)
  have c2 := cells (2,2,0) (by decide)
  have c3 := cells (1,2,2) (by decide)
  have c4 := cells (3,3,1) (by decide)
  have c5 := cells (2,3,3) (by decide)
  have c6 := cells (3,4,2) (by decide)
  have c7 := cells (0,4,3) (by decide)
  have r0 := parityRule F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
  have r1 := parityRule F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c7 c6 c0 c4
  have r2 := hornRule F c2 c6 c3
  have r3 := hornRule F c5 c0 c4
  have r4 := hornRule F c4 c1 c5
  have r5 := hornRule F c7 c3 c6
  exact wQ (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def uA : List PanelTag := [(0,0,2),(1,1,1),(2,2,0),(1,2,2),(3,3,0),(0,3,1),(2,4,1),(3,4,2)]
theorem wR (A0 A1 A2 A3 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A2) → (A2 → A0 → A1) → False := by tauto
theorem k7 : panelClosed 4 uA := by
  intro S T F w p n mem diff cells
  have c0 := cells (0,0,2) (by decide)
  have c1 := cells (1,1,1) (by decide)
  have c2 := cells (2,2,0) (by decide)
  have c3 := cells (1,2,2) (by decide)
  have c4 := cells (3,3,0) (by decide)
  have c5 := cells (0,3,1) (by decide)
  have c6 := cells (2,4,1) (by decide)
  have c7 := cells (3,4,2) (by decide)
  have r0 := parityRule F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c6
  have r1 := parityRule F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c5 c4 c0 c7
  have r2 := parityRule F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c7 c2 c4
  have r3 := hornRule F c3 c4 c2
  have r4 := hornRule F c2 c0 c3
  exact wR (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def uB : List PanelTag := [(0,0,0),(1,1,0),(2,2,3),(3,3,3),(2,4,1),(3,4,2),(1,5,1),(1,5,2),(0,5,3)]
theorem wS (A0 A1 A2 A3 : Prop) : (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (A3 → A1 → A2) → (A2 → A1 → A3) → (A0 → A2 → A1) → (A0 → A3 → A1) → False := by tauto
theorem k8 : panelClosed 4 uB := by
  intro S T F w p n mem diff cells
  have c0 := cells (0,0,0) (by decide)
  have c1 := cells (1,1,0) (by decide)
  have c2 := cells (2,2,3) (by decide)
  have c3 := cells (3,3,3) (by decide)
  have c4 := cells (2,4,1) (by decide)
  have c5 := cells (3,4,2) (by decide)
  have c6 := cells (1,5,1) (by decide)
  have c7 := cells (1,5,2) (by decide)
  have c8 := cells (0,5,3) (by decide)
  have r0 := parityRule F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c4 c5 c2 c3
  have r1 := parityRule F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c8 c7 c0 c1
  have r2 := hornRule F c5 c6 c4
  have r3 := hornRule F c4 c7 c5
  have r4 := hornRule F c8 c4 c6
  have r5 := hornRule F c8 c5 c7
  exact wS (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def uC : List PanelTag := [(0,0,3),(1,1,3),(2,2,3),(3,3,3),(0,4,1),(1,4,2),(2,5,0),(3,5,1),(3,5,2)]
theorem wT (A0 A1 A2 A3 : Prop) : (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (A1 → A3 → A0) → (A0 → A3 → A1) → (A2 → A0 → A3) → (A2 → A1 → A3) → False := by tauto
theorem k9 : panelClosed 4 uC := by
  intro S T F w p n mem diff cells
  have c0 := cells (0,0,3) (by decide)
  have c1 := cells (1,1,3) (by decide)
  have c2 := cells (2,2,3) (by decide)
  have c3 := cells (3,3,3) (by decide)
  have c4 := cells (0,4,1) (by decide)
  have c5 := cells (1,4,2) (by decide)
  have c6 := cells (2,5,0) (by decide)
  have c7 := cells (3,5,1) (by decide)
  have c8 := cells (3,5,2) (by decide)
  have r0 := parityRule F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1
  have r1 := parityRule F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3
  have r2 := hornRule F c5 c7 c4
  have r3 := hornRule F c4 c8 c5
  have r4 := hornRule F c6 c4 c7
  have r5 := hornRule F c6 c5 c8
  exact wT (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def uD : List PanelTag := [(0,0,2),(1,1,3),(2,2,0),(1,2,4),(3,3,1),(2,3,3),(0,3,4),(3,4,2),(4,4,3),(4,4,4)]
theorem wV (A0 A1 A2 A3 A4 : Prop) : (((A1 ∧ A2) ∨ (¬A1 ∧ ¬A2)) → False) → (((A0 ∧ A3) ∨ (¬A0 ∧ ¬A3)) → False) → (A2 → A0 → A1) → (A3 → A1 → A2) → (A0 → A1 → A2) → (A2 → A4 → A1) → (A3 → A2 → A4) → False := by tauto
theorem kA : panelClosed 5 uD := by
  intro S T F w p n mem diff cells
  have c0 := cells (0,0,2) (by decide)
  have c1 := cells (1,1,3) (by decide)
  have c2 := cells (2,2,0) (by decide)
  have c3 := cells (1,2,4) (by decide)
  have c4 := cells (3,3,1) (by decide)
  have c5 := cells (2,3,3) (by decide)
  have c6 := cells (0,3,4) (by decide)
  have c7 := cells (3,4,2) (by decide)
  have c8 := cells (4,4,3) (by decide)
  have c9 := cells (4,4,4) (by decide)
  have r0 := parityRule F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5
  have r1 := parityRule F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c6 c4 c0 c7
  have r2 := hornRule F c2 c6 c3
  have r3 := hornRule F c4 c1 c5
  have r4 := hornRule F c6 c1 c5
  have r5 := hornRule F c2 c9 c3
  have r6 := hornRule F c7 c5 c8
  exact wV (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) (w 4∈F.inner) r0 r1 r2 r3 r4 r5 r6
def uE : List PanelTag := [(0,0,0),(1,1,0),(2,2,3),(2,3,1),(3,3,2),(1,4,2),(0,4,3),(1,5,1),(3,5,3)]
theorem wW (A0 A1 A2 A3 : Prop) : (((A2 ∧ A3) ∨ (¬A2 ∧ ¬A3)) → False) → (((A0 ∧ A1) ∨ (¬A0 ∧ ¬A1)) → False) → (((A1 ∧ A3) ∨ (¬A1 ∧ ¬A3)) → False) → (A2 → A1 → A3) → (A0 → A3 → A1) → False := by tauto
theorem kB : panelClosed 4 uE := by
  intro S T F w p n mem diff cells
  have c0 := cells (0,0,0) (by decide)
  have c1 := cells (1,1,0) (by decide)
  have c2 := cells (2,2,3) (by decide)
  have c3 := cells (2,3,1) (by decide)
  have c4 := cells (3,3,2) (by decide)
  have c5 := cells (1,4,2) (by decide)
  have c6 := cells (0,4,3) (by decide)
  have c7 := cells (1,5,1) (by decide)
  have c8 := cells (3,5,3) (by decide)
  have r0 := parityRule F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c3 c4 c2 c8
  have r1 := parityRule F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c6 c5 c0 c1
  have r2 := parityRule F (mem 1 (by decide)) (mem 3 (by decide)) (diff 1 (by decide) 3 (by decide) (by decide)) c7 c8 c5 c4
  have r3 := hornRule F c3 c5 c4
  have r4 := hornRule F c6 c4 c5
  exact wW (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def panelAt : Nat → PanelProof
  | 0 => ⟨4,u8,k5⟩
  | 1 => ⟨4,u9,k6⟩
  | 2 => ⟨4,uA,k7⟩
  | 3 => ⟨4,uB,k8⟩
  | 4 => ⟨4,uC,k9⟩
  | 5 => ⟨5,uD,kA⟩
  | _ => ⟨4,uE,kB⟩
def panelWires (arity : Nat) (ws : List Sig) (w : Nat→Sig) :=
  (List.range arity).all (fun i => decide (w i∈ws) &&
    (List.range arity).all (fun j => (i==j) || decide (w i≠w j)))
def panelCheck (pc : PanelProof) (ws : List Sig) (T : Sig) (w : Nat→Sig) (p n : Nat→Row) :=
  panelWires pc.arity ws w &&
    pc.tags.all (fun t => kwWireB ws T (w t.1) (p t.2.1) (n t.2.2))
theorem panelAnd {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h
theorem panelCheck_forbids {pc ws T w p n} (F : SingleFactor (List.toFinset ws) T)
    (h : panelCheck pc ws T w p n=true) : False := by
  have ij := (panelAnd h).1
  have hrow (i : Nat) (hi : i<pc.arity) := panelAnd
    (List.all_eq_true.mp ij i (List.mem_range.mpr hi))
  apply pc.closed F w p n
  · intro i hi
    exact List.mem_toFinset.mpr (of_decide_eq_true (hrow i hi).1)
  · intro i hi j hj ne
    have one := List.all_eq_true.mp (hrow i hi).2 j (List.mem_range.mpr hj)
    have diff : (i==j)=false := beq_eq_false_iff_ne.mpr ne
    simpa only [diff,Bool.false_or,decide_eq_true_eq] using one
  · intro t ht
    exact kwWireB_sound (List.all_eq_true.mp (panelAnd h).2 t ht)
def panelWord (pos neg : Nat) (ws : List Sig) (T : Sig) (k rec : Nat) :=
  let field := fun i => (rec >>> (4*i)) &&& 15
  decide (k≤ws.toFinset.card) && panelCheck (panelAt (field 0)) ws T
    (fun i => ws.getD (field (1+i)) zero)
    (fun i => kwProbe pos (field (6+i))) (fun i => kwProbe neg (field (12+i)))
theorem panelWord_sound {pos neg ws T k rec} (ok : panelWord pos neg ws T k rec=true) :
    Impossible false T k ws.toFinset := by
  obtain ⟨bound,check⟩ := panelAnd ok
  intro j hj live
  obtain ⟨F⟩ := oneShare live (hj.trans (of_decide_eq_true bound))
  exact panelCheck_forbids F check
def f1 : Nat := (readWords [38738673928,0x4210842110c0300c03])
def f0 : Nat := (readWords [54056593669,0x68325147434114642a])
def panelTableCheck (pos neg : Nat) (g : Forest) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun i => panelWord pos neg (stateSet g k (start+i)) (targetOf g) k (data i))
theorem panelTableBlock {pos neg g k start n data} (mode : g.mode=false)
    (ok : panelTableCheck pos neg g k start n data=true) : CutRow g k start n := by
  intro j lo hi
  right
  rw [mode]
  have h := List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
  have e : start+(j-start)=j := by omega
  change panelWord pos neg (stateSet g k (start+(j-start))) (targetOf g) k _=true at h
  rw [e] at h
  exact panelWord_sound h
def panelDispatch (pos neg : Nat) (g : Forest) (k i : Nat) (kw panels : Nat→Nat) (tag : Nat) :=
  if tag=0 then nodeVerified g k i else if tag<128 then
    kwWord pos neg (targetOf g) (stateSet g k i) k (packedAt kw (32*(tag-1)) 32)
  else panelWord pos neg (stateSet g k i) (targetOf g) k (packedAt panels (68*(tag-128)) 68)
def panelDispatchTable (pos neg : Nat) (g : Forest) (k start n : Nat) (kw panels : Nat→Nat) (data : Nat) :=
  (List.range n).all fun j => panelDispatch pos neg g k (start+j) kw panels ((data >>> (8*j)) &&& 255)
theorem panelDispatchBlock {pos neg g k start n kw panels data} (mode : g.mode=false)
    (h : panelDispatchTable pos neg g k start n kw panels data=true) : CutRow g k start n := by
  intro j lo hi
  have one := List.all_eq_true.mp h (j-start) (List.mem_range.mpr (by omega))
  have eq : start+(j-start)=j := by omega
  change panelDispatch pos neg g k (start+(j-start)) kw panels _=true at one
  rw [eq] at one
  unfold panelDispatch at one
  split at one
  · exact Or.inl one
  · right
    rw [mode]
    split at one
    · exact kwWord_sound one
    · exact panelWord_sound one
theorem mixedIndex {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g cap)
    (idx : indexedRoot g cap i ws=true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact mixedRoot low geom blocks (Nat.le_refl _) idx
theorem checkedCells {g k start n} (arity rows depth : Nat)
    (proof : cells g k start n arity rows depth := by
      simp only [cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd]
      repeat' apply And.intro
      all_goals decide +kernel) : block g k start n = true := cellsBlock proof

theorem checkedGeometry {g : Forest} {prior : Nat → Nat} (columns autos : Nat)
    (pos : (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) = true := by decide +kernel)
    (neg : (chartSamples g.mask (fun j => (g.samples j).2) == 0) = true := by decide +kernel)
    (col : listPieces (fun c => colCheck g.mask c prior) g.cols columns := by
      simp only [listPieces]
      repeat' apply And.intro
      all_goals decide +kernel)
    (aut : listPieces (fun p => autoOK (targetOf g) (p.map swapRows)) g.autos autos := by
      simp only [listPieces]
      repeat' apply And.intro
      all_goals decide +kernel) : graphValid g prior = true := by
  simp only [graphValid, Bool.and_eq_true]
  exact ⟨⟨⟨pos, neg⟩, pieces_all col⟩, pieces_all aut⟩

theorem lowerFromFull {u m q cap} (rows : List Nat)
    (plain : Impossible u (graphGoal q) cap (vars q).toFinset)
    (mixed : Impossible u (graphGoal q) cap (varsX m).toFinset)
    (essential : fullOK m rows = true := by decide +kernel)
    (target : graphGoal m = graphGoal q := by decide +kernel)
    (sources : vars m = vars q := by decide +kernel) :
    Lower u (varsX m) (graphGoal m) (cap+1) := strong_full essential target sources plain mixed

theorem cutFromKnown {u m cap} {ws : List Sig} {es} (known : Known u es) (ci : ColumnInfo)
    (valid : colCheck m ci (boundsBefore es) = true := by decide +kernel)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws) = true := by decide +kernel) :
    Impossible u (graphGoal m) cap ws.toFinset := cut_root (before_sound es known) ci valid cut

def w1 : Array Nat := #[
  0x2015947530075400,0x801264a130061400,0x6012142630021400,0x248a38642086430,0x6014142630021400,0x8214635a0030510,0x2016947530075400,
  0x250885a290083500,0x801264a130051300,0x801264a130050380,0x268a98675086750,0x2018b4a530085400,0x250885a290072480,0x6894b35842058430,
  0x8214635a0040610,0x32800865a2007610,0xa9462587b4032500,0xa502257890023500,0x2015947530064300,0x801264a130051400,0x850265a1900504a0,
  0x2018b4a530063280,0x1328a4b653086040,0x2045947530075400,0x801264a130041300,0x2018b4a130047160,0x2018b4a530074300,0x201a947530075400,
  0x32800865a2005480,0x65b2142630021400,0x6502152690021400,0x60b2142630021400,0x18202631a0028510,0x801264a130050390,0x892a36842068430,
  0xb624519420050210,0x9a5093b784057340,0xa230690a57016570,0x5890b39842058430,0x8257691a0068510,0x2015947530065400,0xb8262631a0032610,
  0x850265a190050490,0x862008a602042081,0x851264a130061400,0x6012142630021300,0x862008a602064011,0x2016947530064380,0x248a38642064210,
  0x801264a130049280,0xa230690a57005460,0x8257691a0072610,0x268a98675075640,0x80359a7b68064570,0x850265a190050480,0x250885a290069370,
  0x32800865a2007690,0x248a38642075320,0x250885a2900724a0,0x1628a1b620086210,0x85b264a130050380,0x6502152690021500,0x8214635a1040610,
  0x6012142630071300,0x201a947530069400,0x6014142630019300,0xba84519470050210,0x6308b08965063070,0x748a28674064170,0x35a27a2986016750,
  0x6308b08965074080,0x7b8106ab90046301,0x6502152690010390,0x2108b2a531074320,0x8214635a1040910,0x801364a130061400,0xa81413570040210,
  0x9102524b31005320,0x862008a6020640a1,0x2015947530064390,0x20169475300643a0,0x801264a130040280,0x205887a29107a620,0x248a38642079430,
  0x9a5093b784059340,0x5890b39842059430,0x628b1807a2001720,0x32800865a2008720,0x268a98675064530,0xa6020a827606a141,0x6894b35842047320,
  0x80359a7b68075680,0x206887a291083720,0x8244639a0038500,0x248a3b642086430,0x25b4945730057400,0x9230631a24016340,0x5a80b19870058210,
  0x43b60092163274655,0xba84519370025080,0xb64002b51056202,0x32800865a2004370,0x9a5093b784047230,0x7b44819a3067510,0x801264a130031200,
  0x6012142630071200,0x8214635a1080310,0x2051374291082570,0x621413520030710,0x851264a130041300,0x6512142630071300,0x8214635a0030410,
  0x8257691a0067510,0x6012142630081300,0x6012142630091200,0x201a947530058300,0x6b02152690021400,0x2015947530068400,0x6014142630019200,
  0x801264ab32027160,0x801264a130027160,0x32844b36a0015470,0x601bb48230048160,0x801264a130039170,0x801264a130020160,0x60b2142630021300,
  0x2016947530059400,0x2016947530065400,0x2016947530089400,0x628b1807a2001680,0x801264a130040270,0x80359a7b68042350,0x801264a130040870,
  0x253885a290059360,0xb624519420047100,0x801264a130080370,0x250885a290059260,0x2015947530053270,0x6a84b25670028070,0x63b40035069176825,
  0x630bb08965063090,0x64b0218a0017602,0x35a27a2986015640,0x35a27a2986015690,0x945759214050970,0x832008a602042081,0x628b1805a2017580,
  0x430b81a362057160,0x638006a82002451,0x32800865a2006580,0xba84519470047100,0xba84519370036100,0xba84519470049100,0x6a84b25a78036190,
  0x6012142630010380,0x268a98675068540,0x2814835a2040730,0x8351374892043620,0x9a5093b784056340,0x268a98675065840,0x2570945730048300,
  0x25b0945730058400,0x2570945730058400,0xb680519420050210,0xb684519420050210,0x628a18620068210,0x638006a85004681,0x95b264a190040870,
  0x85709ab768046570,0x2015947530085400,0xb426203741029010,0xb624519420040210,0x230881a562068120,0x2844865a2080630,0x810368a13b051370,
  0x8045947b35065400,0x8214635a1030410,0x2051374291032690,0x2018b4a53007a400,0x2051374291043720,0x8214635a1090510,0x2b40352490039400,
  0x2b10352490039400,0x6014142630021300,0x601414263001a300,0xa81413570030210,0x6014142630018300,0x6018b48530085400,0x9102524b31004210,
  0x8015947530064300,0x2015947530095400,0x8015947530095400,0x436b84a263061720,0x8200a6b50046a12,0x18202631a002a510,0x4986852a4b016730,
  0x801264a130040380,0x82b4631a0028400,0x80b264a130050390,0x2016947530064390,0x68b4b35842047320,0x25043542900324a0,0x250885a290079400,
  0x862008a602064191,0xa50225789001a390,0xa502257890012490,0x892a36b48057320,0x9a5093b784046230,0x8b40358490034500,0x892a36b48068430,
  0x896a36842068430,0x892a36b48057430,0x648b1807a2012830,0x9230631a24019340,0x892a36b48067430,0x9a6093b784059340,0x892a368420573a0,
  0x6018b48930074380,0x86a0027958016421,0x80359a7b68053460,0xa6020a8276069a41,0x26a0027950015391,0x6a84b25a78047290,0xa6020a827607a251,
  0x630bb08965063070,0x268a98675064590,0x205887a290061570,0x2308b0a562063070,0x832008a602064011,0x2308b1a56206a170,0x832008a6020641a1,
  0x628b1807a2019720,0x832008a602064091,0x628a18620075210,0x832008a602064191,0x638006a85004671,0x26a00279580153a1,0x26a0027958016421,
  0x6a84b25a78049120,0x8306907b650640a0,0xb8245693a0038400,0x32800865a20076a0,0x2015947530064380,0x80b264a130050380,0x892a36842057320,
  0x801a947b35075400,0x1368a4b653086040,0x8015947b35075400,0xb681519420050210,0x1328a4b653075830,0x250885a290068370,0x601bb48530074380,
  0x801364a130050380,0xb6040a8276083261,0x64b0218a0023812,0x2015947530064a00,0x2106927531064320,0x6890b35842047830,0xb9262637a1032610,
  0xb9452637a1032610,0x6012142630021900,0x6012142630021a00,0x90359a4b68084560,0xa9462587b4021380,0x95036ba198050470,0x5278006a84004671,
  0xa9462587b4019380,0x85b364a130050380,0x7b8006ab90046901,0xa9462587b4021480,0xa644639a0038500,0x7b8106ab90056401,0x6891b35842047320,
  0x2048b4a530085400,0x5628a18620076210,0x6512142630021400,0x8257692a0072610,0x8244635a0040610,0x8015947b30075400,0xb621519420050210,
  0x804a947530075400,0x5628a18620086210,0x4b8609b837058371,0x2054374291043720,0x80b264a130061400,0x2308b1a562079120,0x20b71ba576085213,
  0x7412079541054021,0x26ba98675078650,0x5a80b19870056210,0x62ba18620078210,0x2048b3a542065434,0xba635694a0050610,0x1a80813b70038210,
  0x2108b2a531085320,0x8b2a36842068430,0x862008a602086131,0x850265a190061500,0x18202631a0032610,0x9a6093b784057340,0x832008a602086131,
  0x26a0027958027531,0x90379a7b68075680,0x95046ba198061580,0x7b8006a830068311,0x7b8106ab90068511,0x85026ba098061580,0x86406b0a58016580,
  0x9260631a24016340,0x5896a36842068430,0x628a18620086210,0x59471b9867058123,0x76835894a3050834,0x4687b58294083506,0xa437528749032053,
  0x634ab48935085400]
def wX (codes i : Nat) : Nat :=
  w1[(codes >>> (9*i)) &&& 511]?.getD 0
theorem checkedPanel {g k start n} (codes : Nat)
    (mode : g.mode = false := by rfl)
    (proof : panelTableCheck f1 f0 g k start n (wX codes) = true := by decide +kernel) :
    CutRow g k start n := panelTableBlock mode proof
theorem checkedCut {g k start n} (data : Nat)
    (mode : g.mode = false := by rfl)
    (proof : kwTest f1 f0 g k start n (fun _ => data) = true := by decide +kernel) :
    CutRow g k start n := mixedCut mode proof
def g0 (i : Nat) : Nat := 0xf
def g1 : Packing := (1,0,1,0,0,0,0,g0)
def vS : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xfffffffffffffffff3]),0x62),((readWords [255,0xffffffffffffffffff,0xffffffffffffffffbf]),(readWords [255,0xffffffffffffffffff,0xffffffffffffffff99])),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def vR : List ColumnInfo := []
def tF : List (List Nat) := [[],[48,33]]
def x0 : Nat → Packing
  | 3 => g1
  | _ => emptyPacking
def tG : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def fC : Forest := ⟨15,3,fun j => vS[j]?.getD (0,0),vR,tF,x0,tG⟩
set_option maxHeartbeats 0 in
theorem sS : graphValid fC (boundsBefore []) = true := checkedGeometry 0 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tA : block fC 3 0 1=true :=
  (by decide +kernel)
theorem x5 : checkedTables fC 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block fC 0 0 0 = true)
  · exact (rfl : block fC 1 0 0 = true)
  · exact (rfl : block fC 2 0 0 = true)
  · exact tA
def qC : Array (List Nat) := #[
  [],[101,66,16],[135,50,65],[133,117,101,33,48],[82,129,48],
  [50,65],[115,83,82,130,99,66,16],[130,50,81,115,98,65],[116,83,32],[113,97,82,32,65,48],
  [115,84,99],[128,64,116,81,96,49,32],[83,133,115,67,32,96],[128,16,64,100,80,113,33,48],[117,67,32],
  [135,101,50,33,16,64],[129,98,82,16,66,49,112],[133,117,16,64,49,32],[114,81,98,50,65],[83,114,99,33,16,64],
  [130,50,98,82,115,33,65],[128,100,49,112],[99,132,84,48,33,112],[129,82,97,48],[118,133,33,48],
  [116,100,83,32],[132,65,48,80,113,32],[67,80,100,131,112,32,16],[129,82,113,48],[130,114,98,81],
  [66,114,132,49,32,81,96],[50,117,131,49,32,65,96],[50,33,16,64],[114,33,97,82,50,65],[130,33,113,99,82,65],
  [130,33,50,113,99,82,16,64],[115,67,100,83],[131,115,65,50,98,81],[131,115,100,50,33,16,80],[117,101,67,32],
  [80,84,132,49,113,96],[117,80,66,96,16],[114,83,48,33,97,64],[129,33,97,81,16,114,49,64],[134,81,114,50,65],
  [64,132,49,96],[115,82,98,131,66,16],[98,118,81,130,50,65],[128,80,84,66,16,114,97,48],[132,116,84,48,33,96],
  [132,116,65,48,80,97,32],[66,114,50,132,99,32,80,16],[82,48],[84,115],[80,132,99,112,32,16],
  [131,67,99,116,50,33,16,80],[132,67,100,84,48,33,112],[130,50,97,115,82,16,64],[128,97,65,49,33,112],[129,80,48,50,114,97,64],
  [114,67,84,48,33,97,128],[66,16],[99,83,64,32,16],[115,50,98,83,66,16],[114,98,83,33,16,64],
  [130,114,98,49,32,81,64],[131,50,66,116,99,82],[130,50,116,49,32,97,80],[101,50,33,16,64],[83,82,114,99,66,16],
  [128,81,67,112,97,32],[83,80,132,115,96,32,16],[115,83,67],[101,117,50,33,16,64],[82,98,115,66,16],
  [128,80,117,32,16,98,65,48],[82,50,133,98,49,32,113,64],[49,50,83,48,130,113,64],[113,129,97,82,32,65,48],[99,81,115,130,65],
  [128,64,116,49,96],[131,84,115,98],[130,114,98,33,81],[82,133,99,49,32,65,112],[128,84,66,16,98,113,48],
  [131,65,50,114,81],[130,33,113,98,66,16,80],[128,80,81,67,96,113,32],[84,117,80,132,96,48,32,16],[118,130,81],
  [80,48,50,114,129,64],[100,131,82,16],[100,131,116,50,33,16,80],[33,80,112,97,130,49,64],[117,80,66,130,96,16],
  [84,131,98],[64,48,32,16],[80,64,48,32,16],[32,82,64,16],[96,80,64],
  [48,96,83,64,32,16],[115,99,83,67],[112,96,48,50,33,81,64],[114,50,99,48,33,81,64],[115,99,82,64,16],
  [115,96,83,64],[131,115,99,50,82,65],[131,115,50,98,83,66,16],[131,115,99,82,64,16],[130,114,49,98,81,64],
  [131,115,98,83,66],[131,115,98,83,32,64],[130,114,97,82,16,64],[130,50,115,98,49,32,81,64],[130,50,115,49,98,81,64],
  [48,128,115,96,50,33,81,64],[129,33,115,48,98,81,64],[32,50,128,115,98,81,64],[82,98,66,16],[131,67,116,99,82,16],
  [131,115,99,67,82,16],[128,112,96,49,64],[131,115,83,67,98],[129,113,82,65,48],[80,81,129,114,50,65,96],
  [81,33,80,128,97,114,49,64],[98,99,81,131,114,65],[48,84,100,49,129,112],[33,32,65,48],[16,64,49,32],
  [113,16,96,81,49,64],[129,113,33,98,81,48],[130,114,99,49,32,65,80],[129,113,98,16,66,49,80],[129,50,114,48,66,97,80],
  [129,116,50,97,80],[115,50,32,83,66,96,16],[112,48,50,33,97,64],[99,115,83,48,33,64],[83,80,96,115,64,32,16],
  [81,80,48,50,130,113,64],[117,101,33,32,65,48],[129,113,82,97,48],[129,33,114,82,16,66,49,96],[132,67,84,48,33,113,96],
  [128,16,113,65,49,33,96],[82,50,133,115,49,32,65,96],[81,80,128,113,98,49,64],[82,48,66,112],[83,114,64],
  [117,130,99,32,64,16],[116,100,49,81,32],[115,83,133,99,50,66,16],[84,100,49,128,113,32],[131,100,115,82,16],
  [134,117,33,32,65,48],[84,133,80,66,114,96,16],[82,48,66,129,112],[67,132,99,82,16],[117,99,49,32,65,128],
  [100,49,128],[118,101,133,50,33,16,64],[98,82,16,66,49,128],[84,66,16,98,129,48],[80,81,114,66,50,129,96],
  [116,50,129,80],[116,100,49,32,81,128]]
def extendPerm (old : List (Nat × Nat)) (bound : Nat) (entries : List (Nat × Nat)) :=
  extendKnown old bound (entries.map fun p => (p.1, qC[p.2]?.getD []))
def qH := extendPerm [] 4 [(15,0),(23,96),(27,61),(29,5),(30,32),(39,97),(57,98),(78,99),(83,62),(99,100),(135,101),(156,102),(163,63),(165,33),(166,64),(172,103),(177,104),(198,105),(281,106),(291,107),(300,65),(305,108),(312,109),(323,110),(326,111),(330,112),(332,113),(344,114),(353,34),(354,35),(396,115),(424,116),(480,117)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem uF : Known true qH := extend_ok (m:=15) baseKnown
    (plain_low (hints:=8449) (by decide +kernel) (index_root (g:=fC) (i:=0) rfl rfl (before_sound [] baseKnown) sS x5 (by decide +kernel))) (by decide +kernel)
def g4 (i : Nat) : Nat := 0x11a20bf
def g9 : Packing := (1,0,3,0,0,0,0,g4)
def g6 (i : Nat) : Nat := (readWords [48,0xbe6702080000650000,0x16357504004755c084])
def g3 (i : Nat) : Nat := 0x40828fd20fd10
def g8 : Packing := (2,1,3,0,0,3,0,g3)
def g5 (i : Nat) : Nat := 0x300
def g2 (i : Nat) : Nat := 0x5dd4520
def g7 : Packing := (1,2,3,0,0,0,0,g2)
def vX : Array (Bits × Bits) := #[(0x2e44,0x2c52),(0x5a8a,0x5208),((readWords [255,0xffffffffffffffffff,0xffffffffffffffb4f7]),(readWords [255,0xffffffffffffffffff,0xffffffffffffffa0c7])),((readWords [255,0xffffffffffffffffff,0xffffffffffffffcf79]),0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def vW : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def wH : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x3 : Nat → Packing
  | 6 => g9
  | 5 => g8
  | 4 => g7
  | _ => emptyPacking
def tH : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 15 3 9 1 4 g6
  | 5 => lookupWord 1 3 1 9 1 4 g5
  | _ => fun _ => none
def sF : Forest := ⟨31,6,fun j => vX[j]?.getD (0,0),vW,wH,x3,tH⟩
set_option maxHeartbeats 0 in
theorem sT : graphValid sF (boundsBefore qH) = true := checkedGeometry 0 1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tD : block sF 6 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tC : block sF 5 0 2=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tB : block sF 4 0 1=true :=
  (by decide +kernel)
theorem x6 : checkedTables sF 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block sF 0 0 0 = true)
  · exact (rfl : block sF 1 0 0 = true)
  · exact (rfl : block sF 2 0 0 = true)
  · exact (rfl : block sF 3 0 0 = true)
  · exact tB
  · exact tC
  · exact tD
def u5 := extendPerm qH 7 [(31,0),(167,36),(313,37),(334,38),(355,66),(428,67)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem uG : Known true u5 := extend_ok (m:=31) uF
    (plain_low (hints:=8449) (by decide +kernel) (index_root (g:=sF) (i:=0) rfl rfl (before_sound qH uF) sT x6 (by decide +kernel))) (by decide +kernel)
def u6 := extendPerm u5 5 [(61,5),(91,1),(94,68),(181,18),(227,69),(230,19)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem uH : Known true u6 := extend_ok (m:=47) uG
    (plain_low (hints:=8449) (by decide +kernel) (cutFromKnown uG (8,0,39,0,4))) (by decide +kernel)
def u7 := extendPerm u6 5 [(55,0),(59,5),(103,118)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem uI : Known true u7 := extend_ok (m:=55) uH
    (plain_low (hints:=257) (by decide +kernel) (cutFromKnown uH (16,0,39,0,4))) (by decide +kernel)
def qI := extendPerm u7 8 [(63,0),(95,1),(159,39),(359,119),(377,70),(462,12),(483,71),(492,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem uJ : Known true qI := extend_ok (m:=63) uI
    (plain_low (hints:=8449) (by decide +kernel) (cutFromKnown uI (32,0,31,0,7))) (by decide +kernel)
def f8 (i : Nat) : Nat := 0x7213f
def fB : Packing := (1,0,2,0,0,0,0,f8)
def f9 (i : Nat) : Nat := 0x8000
def f7 (i : Nat) : Nat := 0x17e51
def fA : Packing := (1,1,2,0,0,0,0,f7)
def wC : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xffffffffffffffed93]),0x2d12),((readWords [255,0xffffffffffffffffff,0xffffffffffffff9467]),(readWords [255,0xffffffffffffffffff,0xffffffffffffff9025])),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]
def wB : List ColumnInfo := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def uY : List (List Nat) := [[],[32,83]]
def vQ : Nat → Packing
  | 6 => fB
  | 5 => fA
  | _ => emptyPacking
def uZ : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 f9
  | _ => fun _ => none
def j9 : Forest := ⟨111,6,fun j => wC[j]?.getD (0,0),wB,uY,vQ,uZ⟩
set_option maxHeartbeats 0 in
theorem tI : graphValid j9 (boundsBefore qI) = true := checkedGeometry 0 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uN : block j9 6 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uM : block j9 5 0 1=true :=
  (by decide +kernel)
theorem y1 : checkedTables j9 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block j9 0 0 0 = true)
  · exact (rfl : block j9 1 0 0 = true)
  · exact (rfl : block j9 2 0 0 = true)
  · exact (rfl : block j9 3 0 0 = true)
  · exact (rfl : block j9 4 0 0 = true)
  · exact uM
  · exact uN
def q9 := extendPerm qI 7 [(111,0),(123,1),(187,41),(190,42),(215,72),(222,73),(238,19),(243,74),(311,120),(318,121),(343,122),(349,75),(365,123),(378,43),(437,44),(455,12),(476,76),(485,124),(490,125),(497,126),(504,77)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v0 : Known true q9 := extend_ok (m:=111) uJ
    (plain_low (hints:=16785665) (by decide +kernel) (index_root (g:=j9) (i:=0) rfl rfl (before_sound qI uJ) tI y1 (by decide +kernel))) (by decide +kernel)
def fF (i : Nat) : Nat := 0x163441bf
def fK : Packing := (1,0,3,0,0,0,0,fF)
def fH (i : Nat) : Nat := (readWords [0x42f9f28c08140000,9279884095127760])
def fE (i : Nat) : Nat := 0x420a3fa41fd10
def fJ : Packing := (2,1,3,0,0,3,0,fE)
def fG (i : Nat) : Nat := 0x18000
def fD (i : Nat) : Nat := 0xb7d8d20
def fI : Packing := (1,2,3,0,0,0,0,fD)
def wE : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xfffffffffffff55417]),(readWords [255,0xffffffffffffffffff,0xfffffffffffff46453])),(0x0,0x0),((readWords [255,0xffffffffffffffffff,0xfffffffffffffc60f7]),0x44076),((readWords [255,0xffffffffffffffffff,0xfffffffffffff0bbcb]),(readWords [255,0xffffffffffffffffff,0xfffffffffffff03a89])),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]
def wD : List ColumnInfo := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def jA : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def vT : Nat → Packing
  | 7 => fK
  | 6 => fJ
  | 5 => fI
  | _ => emptyPacking
def x1 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 13 2 9 1 4 fH
  | 6 => lookupWord 1 3 1 9 1 4 fG
  | _ => fun _ => none
def qJ : Forest := ⟨189,7,fun j => wE[j]?.getD (0,0),wD,jA,vT,x1⟩
set_option maxHeartbeats 0 in
theorem tJ : graphValid qJ (boundsBefore q9) = true := checkedGeometry 1 2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uQ : block qJ 7 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uP : block qJ 6 0 2=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uO : block qJ 5 0 1=true :=
  (by decide +kernel)
theorem y2 : checkedTables qJ 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block qJ 0 0 0 = true)
  · exact (rfl : block qJ 1 0 0 = true)
  · exact (rfl : block qJ 2 0 0 = true)
  · exact (rfl : block qJ 3 0 0 = true)
  · exact (rfl : block qJ 4 0 0 = true)
  · exact uO
  · exact uP
  · exact uQ
def wL := extendPerm q9 8 [(189,0),(303,2),(347,20),(486,6)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v2 : Known true wL := extend_ok (m:=189) v0
    (plain_low (hints:=536879876) (by decide +kernel) (index_root (g:=qJ) (i:=0) rfl rfl (before_sound q9 v0) tJ y2 (by decide +kernel))) (by decide +kernel)
def qA := extendPerm wL 9 [(127,0),(382,21),(478,22),(508,127)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v1 : Known true qA := extend_ok (m:=127) v2
    (plain_low (hints:=16785665) (by decide +kernel) (cutFromKnown v2 (32,0,95,0,8))) (by decide +kernel)
def sG (i : Nat) : Nat := 0x8201ff
def sI : Packing := (1,0,5,0,0,0,0,sG)
def sH (i : Nat) : Nat := (readWords [0x99090000b500,458852568751104,0xe4006080015749fa6,0x141c73802b0a68137,0x976081bca199eaaa3d,0x961388c0f3a0002328,0xc00084a05000089c2a])
def fO (i : Nat) : Nat := (readWords [2,0x88616180c48a1166c0,0x8c818588a2e004e68,0xc2c214019ce18588b2,0x410102944c300431c5,0x89360181384080512,0x18b0c0328614b0a030,0x139610c0803944862a,0x8614888704038c2842,0x4018278d600745a25b,0x53e43cce27c5e0bc00,0xff483fe30ff4c3fd10,0xff54ffe10ff903fe20,0xff4c7fc20ff58ffd40])
def fV : Packing := (12,1,5,0,0,10,0,fO)
def fR (i : Nat) : Nat := (readWords [351843720888320,0x198cb0000a04e08a,0x520001a51c20000531,0xe80b64388d00078963,0xd80a7524800343b41a,0x670800007a7cc632d7,0x5239502d6072864000,0x60840000002a,0x100028a67e35dbbd50,0x1a6c315cd7a0d113,0xac2700012180005256,0x8158594ec000682af9,0xf6880000010b6f,0xab800321ac31374a97,0xc0018068243a2b09f0,0x6ef8c8000c984c7fad,0x8000732e29d36fd3c9,0xba4660000003c50a43,0xa2e72f0000037c5c48,0x4413000060966343d5,0x67081fd24000161fd8,0xfb857db1616c2d70bc,0x1da504981c000a8,0xcb68709baa54393350,0x153817e93b2ee08a0b,0x35c971e4812648c40c,0xf0c890074a5b901b85,0xc19b060f0f30f9c6d4,0x6f822909e468ae58b6,73289049124639786,0x8dc0d2c800031c6000,0x5ad28d4a6000000000,0x4610000000000,98371931427008,0x7fc419a5a33000612d,0xc38451b04000033fe5,0x70000002d76000244c,0x429f180a5d34b0ba13,0x60001a731afd48a565,0xb2f860060014b1d811,0x1aaaac600056d80000,681893276580045,0x5b803ae00010d91906,0xc6000000173ec82c42,0x58c80000000001b,0x509c9847ce37e90001,0xc466a9e954000000c9,0x9484d7ca82a800f934,0x47182024f80000c48d,0xc000596030083ad05a,0x1c75006c1081741081,0x4060062c3582005184,0x1c00801071c96460c2,576628352389259,0xc0000080000041016])
def fN (j : Nat) : Nat := (readWords [528495944,0x99e077b024a9159a24,0xb911ac077e0465c892,0x708574212ef090d670,0x221e053c214e043b82,0x35cc808a67d091c046,0xf022c0a32623f70495,0x22d15433a6477b08ce,0x33e84719314e04222,0xc097484381b79046f2,0x83ea431f521b80ae4,0x46e02b90c91ffb0022,0xff500273ff780227d0,0x9160ad1a2b008a388,0x648213e1129ec12370,0x1bbc02b6031f108e81,0x2788527a1372fef00a,0x370177821af58220f9,0x8488d80ed11b79e031,0x29f81224fe00116e0,0x8ea457911b01380878,0x4866ffa009e7c49103,0xfc0098ee0495c8319f,0x848269f5444bf2292d,0xf046e02b7ba00a2fc6,0xc027b211cfe48667a0,0x4ad80ec912592247ef,0xae68147aaa443fce,0x6009d00860143e0495,0x227c608ef0062ec24c,0x9e99123806bc624482,0x87a25ec8251c78110a,0x11258898fc21534520,0x9610e8c37008430004,0x14019102020c60a121,0xc5c5ec5844fc4543ec,0x3542cc25c1bc12409b,0xfebf43e8be1bd8bcf3,0xc73b9bae3a7b9eb983,0x8f383b7d373369b603,0x5934fb46b3ab3432bb,0x24b1b311b072fcaf62,0xedae72dc2ce2bf2b02,0xa2294a8da83a7ca70a,0x66a5ea54a4d24423c2,0x33a2aa192102069fa9,0xed9e61de9d29cd1c09,0xb21aa1a399a99498e1,0x8397416815a14f9449,0x3712b11e91590f1000,0xf10e88dd8d18ca0c08,0xb70ab8a209508407d8,0x7606b86505b8510420,0x3883182501880d0004,0x2a470a82c2e250b1c4,0x28051315c2a4b0980c,0x2c730b01c220f0b994,0x2c37098142e4308834,0x28431b894240f098cc,0x2a090881424370b12c,0x240d090ac4e43090cc,0x6e650994426530b0d4,0x4651090d4242f0b98c,0x2a490b0242c570b154,0x2c490b02c2408c3891,0xae246b94ba4107b92b,0x6e24e8849aeb66b881,0xee82a983aa6486b951,0xae707b831ae0c6bad3,0x64307b893a2047b923,0x24287b8ba6e867bb19,0xae0e6bb51ee2a7b909,0xae2c6ba49aed66b9c9,0xae607b8b1ee088a159,0xae50e9811ee4ea9821,0xeea8c98c2a60c6b921,0xae086b8b9ee467bb29,0xee62e9849ae346b8d9,0xee647baa9ee0e6b993,0xa4146b8caa64e6ba41,0xeea67b89b2a286b959,0xae4e7bb216e242b9c8,0x6e87ffff7f7efefbfd,0xf6ef6f902308821058,0xd53501314c12044020])
def fU : Packing := (113,2,5,589836,68,12,1057,fN)
def fQ (i : Nat) : Nat := (readWords [62487568815043,0x679268754bc6188000,0x1bef920589c626a6,0x500070140c8d5de5f1,0xd7a21d0344d98ee800,0x183ee4880000011197,0x1a189f7ac18d073c4,0x1c5a460f2f6dbb0d3e,0x90a06b82f5bcc02928,0xe3aa852e880000109c,0x34616429775d57a008,0x41de8968c753cd4f77,0x79436ba625de899899,0x71c11166c07285d41,0x58b1c40cba3819701f,0xf1ed4e0000001d75e3,0x86545f25c03c4e3ccf,0xe7905e221777000000,0xa100005011f899118,0x6d800000144100008f,0x313025a433c0cd88da,0xe660be94000121c000,0x2c88000000655b0,0xaf52342fd8c3fbe11d,0x39049a5a1e7325180,0x4d4e9a308f4f4000,0xef1802b07e014ce,0xa170acb800000009b4,0xc4008e61bc79a059a0,0xf70fccb137f85b2554,0xdc0000000f21e93d12,0x600012580034900000,707721288482816,0xb1c00000000031850,0x23a5319608aa000191,0x347800000000000000,0x4662140000000000,0x5b0dc8e00000042,0x6e6c726f99d415a6c3,0x45000127023e070c8,0xd80b889403631ef964,0xfdd2196b35879ca860,0xc0656093c9b66e604e,0x1a08c20003c8494d72,0x28964094caf59a8139,0xa149ac000c15105044,0x2c0100242082111,0x47148207881095147,0x80042047000002000,0x1001c02830c5040001,0x40080040540040204,0xc00080070800c1,0xd0040151000c0,0x40141188000004000])
def fM (i : Nat) : Nat := (readWords [616011088138240,0x2c2161020800838410,97068458967072,0x808400418108150880,0x8200a81105842c3401,0x8081882c400010401,0x610060400004128800,0x6508824200028421,0x410000c01624108000,0x7085060424a100000,0x220d0042c200002c20,0x410018408210b0d084,0x384082c4121090,0x80006109020848e842,0x5084082000000006,0x1881c2121000008bf,0x14a22c388670ba10c1,0x480f009fabe87c6f79,0xecbd479ef09d6ba873,0x6e39c4b7c6ded69a6b,0x48666c998cb0c5febe,0x972ae05b6b3964abc5,0x6eaa952aa0536a1940,0xa7c4ee9892aa504969,0x191ca2c44e8890ea08,0x3f67d8f89ec3be748e,0x29b83666b8d49a432e,0x628be9782e65b8b095,0x429e5089e930246458,0x8890c20e3e8728d819,0x6318608bc15e248428,0x800f61b83085c0ae14,0x8268480860b8108140,0x1e02802800df4815ca,0x209fd879c9109fd82d,0xc163df5215c620aff8,0x654931ff38148230fe,0x92054930df7715c520,0x9fd82dd530b7f85581,0x40bf7815c520bbf844,0xc1209ff815c163df77,0x1501209ff815c1539f,0xd81dc163fe92048630,0xdf920dc530ff210dc5,0x209fd825c640f75515,0x4131bf78148131df78,0x15ca10df7815ca40dd,0xf714c163bf7815cd20,0x9fd8798a409ff815ca,0x20fd5514c131df9724,0x4220bf9809c910dbf7,0x4549309ff805c5639f,0xd81dd930ded20dc963,0xcfd764c620df4815ca,0x40bf9808ca10b7f855,0x81319fd82dc530df92,0x5c630ff210481319f,0xd80dc5539fd81dd530,0xbbd849c910bf58158e,0x109ff805c963aff865,0x4940ddf714c963df77,0x15cd209fd80dd9319f,0xd82dc563df551dc131,0xddd215ce20df7714c1,0x20fe92050910df5315,0xca10df783dc5209fd8,0x25c630ded52dc931db,0xd425d640df610dd931,0x9ff815cd20bf781481,0x63df5515c1319fd82d,0xc540ddf764c1319fd8,0x78ca109fd81dcd209f,0xd80dc5639ff815ca40,0xdbd54dc940ff110dc5,0x20dbf7458130ded215,0xca30df5615d210bbf8,0x44c110ff081482309f,0xd82dd1109fd82dd540,0xdf471dcd20df771441,0x20bbf845cd20dbd425,0xc640bf7814ca10ff37,0x14c120bdf8350910bf,0x78148153df7215d210,0xbf78158131fe520485,0x31bf78154131ded724,0x8640cfd764ca209ff8,0x15c963bbf845cd10df,0x583dc520edd6358130,0xdf4715cd20df771dcd,0x20ddf714c153ff0714,0xc120fd5314ca109f78,0x15c5209f7815cd209b,0xf845c1539ef825c563,0x9bf845c1639bf845ce,0x10fe120c861097f855,0xda408fd86dd5319bf8,0x45cd209bf845c1319f,0x7815ca409f581dc163])
def fT : Packing := (116,3,5,0,0,11,0,fM)
def fP (i : Nat) : Nat := (readWords [0x30450ac641c006,0x2400b2c00a0c810000,0x1c50000042a883a])
def fL (i : Nat) : Nat := (readWords [59906623710,0x6543ca1408fb4c102b,0x944193f85dd1604c23,0xef22c16eaa062fe1b7,0x454930cdbc26e29824,0x11f79161e6290336f0,0x838ae69056de5183dc,0x5208fb4c0e2b9a419b,0x784dc5734823ef22c1,0x6ea9847de4582dd110])
def fS : Packing := (12,4,5,0,0,6,0,fL)
def wG : Array (Bits × Bits) := #[((readWords [255,0xfffffffffffffda8e8,0x1df4649a4aea03f353]),(readWords [108576,0x9cc44085084a802052])),((readWords [255,0xfffffffffffffe5506,0x27bdd1589ea381610f]),(readWords [255,0xfffffffffffffe550c,0x23b884896b1415109])),((readWords [47222,0xf0435535c500a8ea8c]),(readWords [10354,0x300045166108a00a84])),((readWords [157341,0xfd182653b341a80c0]),(readWords [148108,0xbdd82211a84129140])),((readWords [87361,0x72223bd2f53d4f48e0]),(readWords [5441,0x6022395ae5314d4aa0])),((readWords [152506,0x8288d622045549630]),(readWords [151710,0x22805626105509220])),(0x0,0x0),((readWords [233217,0xc59fba0814d3746c20]),(readWords [100097,0xc597ba0892d2056500])),(0x0,0x0)]
def wF : List ColumnInfo := readRows 32 (fun x => (readField x 0 8, readField x 8 8, readField x 16 8, readField x 24 4, readField x 28 4)) 21 (readWords [4200192,0xa840a6001940270098,0x401d00a24039008640,0xa5001a40870038409c,0x2340b1000e40a308,0x1440a61009401e2081,0x50370088401b802470,0xbe000170bb000469a6,0x100040ac001380bd00,0x270a70018701f00a0])
def qE : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def vV : Nat → Packing
  | 10 => sI
  | 9 => fV
  | 8 => fU
  | 7 => fT
  | 6 => fS
  | _ => emptyPacking
def x2 : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 41 5 10 4 2 sH
  | 9 => lookupWord 67 277 6 13 7 2 fR
  | 8 => lookupWord 100 251 6 13 7 2 fQ
  | 7 => lookupWord 4 19 2 10 4 2 fP
  | _ => fun _ => none
def zX : Forest := ⟨191,10,fun j => wG[j]?.getD (0,0),wF,qE,vV,x2⟩
set_option maxHeartbeats 0 in
theorem tK : graphValid zX (boundsBefore qA) = true := checkedGeometry 3 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vM : block zX 10 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uU : block zX 9 0 12=true :=
  (checkedCells 8 0 2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uT : block zX 8 0 113=true :=
  (@block_merge zX 8 0 106 7 (@block_merge zX 8 0 70 36 (@block_merge zX 8 0 39 31 (@block_merge zX 8 0 3 36
  (by decide +kernel)
  (checkedCells 8 0 3))
  (checkedCells 8 0 3))
  (checkedCells 9 0 3))
  (checkedCells 9 0 1))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uS : block zX 7 0 116=true :=
  (@block_merge zX 7 0 85 31 (@block_merge zX 7 0 49 36 (@block_merge zX 7 0 13 36
  (checkedCells 7 0 2)
  (checkedCells 8 0 3))
  (checkedCells 8 0 3))
  (checkedCells 8 0 3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uR : block zX 6 0 12=true :=
  (checkedCells 7 0 2)
theorem y3 : checkedTables zX 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block zX 0 0 0 = true)
  · exact (rfl : block zX 1 0 0 = true)
  · exact (rfl : block zX 2 0 0 = true)
  · exact (rfl : block zX 3 0 0 = true)
  · exact (rfl : block zX 4 0 0 = true)
  · exact (rfl : block zX 5 0 0 = true)
  · exact uR
  · exact uS
  · exact uT
  · exact uU
  · exact vM
def wM := extendPerm qA 11 [(191,0),(319,2),(351,3),(367,13),(379,7),(431,78),(445,23),(487,6),(494,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v3 : Known true wM := extend_ok (m:=191) v1
    (plain_low (hints:=536879361) (by decide +kernel) (index_root (g:=zX) (i:=0) rfl rfl (before_sound qA v1) tK y3 (by decide +kernel))) (by decide +kernel)
def wN := extendPerm wM 8 [(251,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v4 : Known true wN := extend_ok (m:=251) v3
    (plain_low (hints:=1358970881) (by decide +kernel) (cutFromKnown v3 (128,0,123,0,7))) (by decide +kernel)
def qB := extendPerm wN 12 [(255,0),(479,24),(503,46),(507,79),(509,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem v5 : Known true qB := extend_ok (m:=255) v4
    (plain_low (hints:=553656577) (by decide +kernel) (cutFromKnown v4 (64,0,191,0,11))) (by decide +kernel)
def sL (i : Nat) : Nat := 0x1840804ff
def sR : Packing := (1,0,6,0,0,0,0,sL)
def sO (i : Nat) : Nat := (readWords [3167806819908,0x28954b00129713b90,0x21c5c400a24a286e0,0x30000000000d800006,0x790000005048cec0c5,0x84c000029410000109])
def sK (i : Nat) : Nat := (readWords [494230678538304,0xa80c160880850c1604,0x287044044070d0e042,0x82102a03050f061043,0x70d0a085086803613,0x65e17803fe087fc30f,0xfa61ff443ff187fe10])
def sQ : Packing := (6,1,6,0,0,9,0,sK)
def sN (i : Nat) : Nat := (readWords [0x605ec8c000000111,0x7d3d8e632bfc434126,0xa560a0c97cd1c2e000,0x6879dce01300020298,0x32241d31f89848e708,6943248552,0x1d83401050198b41ca,0x520a2f40adbada2902,0x70002212000f024055,0x5b3c62d0c010b44640,0xb0000000000a020000,0x274e000193000140,0xac0e19590854ad6249,0xde02102d21d615614,0x2944000d8a4082dc48,0x550007f79444000141,90670475577393152,0x58000991281875380f,0x661504984eda4b2e78,0x7cc39625232a002653,0xd245061c2fea200000,0x680400000024e94b1,0x850b1ad21701010060,0xb00017050301c0500,0x70e260404451400410])
def sJ (j : Nat) : Nat := (readWords [767,0x45022545810b0ebed2,0xa0a0caa9a4a6461701,0x18bba1216fab28127d,0x3e208a4fd302575680,0x8373fd0139d909a4f7,0x7fc6205153e0263c3e,0x95f7f520157b044d7,0x7c804c7e9c8080acf7,0x959fa41af7f15139,0xe7a243e4b049e3e725,0x49ef82c4149a9b213c,0xd771046be348414dff,0x820a1d72484df8820,0x50f8046fdd00eb5019,0xeb3818801d311052ae,0x460a7bcd01029a0290,0xf738439afc1100200,0xb730408c90182a2e28,0x830c2c20863024850e,0x8b0a261b081c11808f,0x861e128c0d84221782,0xe140a0933257c918e,0x31461a4187eaf6de1b,0xa2708d81a3b2d618bd,0x16c2b1532a053124b4,0x5a834f71d2366648b8,0x95627049c860f91c23,0x445d09f1081b43084b,0x6209c0e800eb8beb9,0xaeb83eb98e398eb9cf,0x41aeb8df389e982e39,0xce41af982fc0bf40bf,0x38de98ce98df39cf18,0xdec0beb89e389fc1af,0x98cec1ae40bfb8dbc2,0x3cb858c1a8c0d8c188,0xc1d8c0c8c098c3dcb8,0x39c0b8c1c9c1a54180,0xc316c156c104c183c2,0x3ffffefbeffbeef7bb,0xebf8c2104c1100c010])
def sP : Packing := (47,2,6,524294,51,11,1060,sJ)
def sM (i : Nat) : Nat := (readWords [7,0x1198115833604b01a0,0x606e88fc000242d,0x7c1fb0faad28000000,0x90720000000000000,310474596682078,0x7a03c800000002072,0xb0000f0374218000,0x83d74340000000000,0x10fe000191d800038,0xc8000000000050001a,0x19c0000000f0d80002,0x417105f0001002bc08,0xec1b0001e12c000000,0xf0e7e92d81a680100,0x81e2997c07b60460,0x2f86e047b093591c,0xb42863642440b4814,0xa40900000001016701,0xf80992cbb0308000c1,0xb416439d943b147aa,0xe00000001400000000,0x51cc437e4b4604d433,0x68120000516302b9f1,0x4067d0c804300,0x61b56b100000c580,0x783f104c0003,0xfbb80009070d07382c,0x4f54000000014a4104,0x60001715080ea87408,0x33a5880002404721a4,0x1d7010e870e0a60000,0x41e7802d68a0000000,1537694969235,0x36823a9a000d7e20d8,0x6d416e10a400828f54,0x40c813b83e60a220d8,0xfa1581020e4099e819,0x7842301210c9aa8083,0x57404e01fd304041e1,0x23c6482e6b2cf063e,0x21e71a6056370a0032,0x1825400056b139c29,0x3c35f0f8311d903113,0x2ca772115827b06218,0xa0203561cf86910f5a,0x5f4b8b233b382b58ee,0x49dec3300d7802d8c0,0x502fd10109b0c0a907,0xee0a0fc274022d3a10,0xd5060b108505d001d3,0xc31732301838cca179,0x204071480aad97c1b,0x8000509cd0a402a948,0x2901e3171c30000064,0xac78e80004854e040d,0xdec841106f32a0420d,0x715820cb2810092535,0x383b24a5005e832182,0x80109ecf40006a47e0,0x540003c1d6c17800c8,0x4f7001b077b0900001,0xc268000e088000143b,0x221e2f0000390d0004,0xc17340800211f0400,0xc3852005c082b0403,0x102880201024c3d0e,0x17000f051141010057,0x3e0400120007050001,0x6400040b010407000d,72624946333089802,0x10e07000000003720])
def fY (j : Nat) : Nat := (if j<1 then (readWords [0x90c4083f321d6c,0xc55f504646019c4420,0x4dfc10cf28937f0432,0x53910ce223b024009,0x80bbc34c65818045e5,0xf095406f016f31822b,0xf789912c221f5c01,0x14f24249ce0e08c5fc,0x120656c06b2083990d,0x70859f222641714118,0x12e90b633045ad9356,0x4ac98ac1927756b1df,0x4473c74045ae40c7bc,0x4213fdaa08c1dec4c9,0x7b82425ed04f3d690c,0x2f0864391ec72208d3,0x90a7d7c922807c0191,0x10fa1911e02bfb824,0xe4c43990d011c06bd,0x692267e463b811dee0,0x91ec041cc873e3c904,0x6de215e623de216f10,0x97a08640ab2623f980,0x4abea9226f20245bf6,0x30932fde02207c2399,0x86b88877f60496e23,0x9ac50c021f5491180a,0x7108bc843247a20643,0xec231f50022efe0c11,0x4fda0958225a38918c,0x18c308840c70fd088c,0x683056b01e8ec1e8c,0xc2c288d0b416286c21,0xc0109148e1a8287387,0x84a282029c20384833,0x40b05c2684e081412,0xe020441e0b05549d4,0x1d33d27d1c513d084f,0xe4f74f14e5cdecd84d,0x14ca4c34bccb4cab49,0xf497c8747fc77c70c6,0x6c60c57c51442437c2,0xfc26c1ec1440dc02bf,0x9beb3e4bddbd73cc3c,0x23b73b1ba83a139739,0x238c37fb78b73b6635,0xfb58b4ab4433833132,0x2317307af72efae7ad,0xe2d5ac72bcab6aae2a,0x129328a280a74a6ba5,0xd251a49237a29a1f21,0x1a061fb9f29e39dc1c,0xc9be1b89ac1a519918,0xf98618097996c96115,0x894e14513b92b12291,0x91109080fd8f80ef0e,0x18d48c70b88aa8a109,0x788d88187906e06905,0xc05604e04083302901,0xa80c00049718e4c0b3,0x6e11290e6d2997424c,0xb9261cf970e52b973,0x15cb95261d8532e4ab,0x97614cb9ca65cf532e,0x6a997744cc1735c271,0x330008982c5cc02266,0x41130937948c5c8c8,0x266017b0528b970cfc,0x91846550c2628b9836,0x12c82e3e58513308c2,0x711a9cabe265d58302,0xaba833c4cc325e5138,0x2e23159451dc19c266,0x176322389989d3c83c,0x2e5cc7ce6137946d3c,0x830e65c3372688b976,0xda48ace60cf232a425,0x9095ec14c266267306,0xa5900054c162a6121,0x72f0bd97886cb3afa4,0x62c1268bd9189c4b86,0xf5cc2173103d8201fb,0x9848644e7b05036915,0x9bc8acde1134322bd7,0x8445bc222c61857b27,0x1159411bc2251e61f1,0xf2d03d829e140aac61,0x88772e19f924dcc192,0x26608830280998704c,0xb8c2e6194b213c5837,0xe0c0bc2e5c62f28537,0x84553c8182661d7306,0xeb784512c83aca4477,0xf2460998808ca9a465,0x4e3f24c3a970dec13d,0x8cc513f24f0b9815f4,0xbc574c555b0f009973,0xddc194de1106b22b09,0x98943c9180e51b0729,0x1ff6febfbff77deefd,0xbff7f6fddf7bdf77eb,0xfcff7feff5fdbf77de,0xf7ddfb7f3fe7dcefdc,0x6309c6308c63061e30,0x60e3060a30606305c6,0x305c2304c630cc6109,0xce1060e10606105ce1,0x4c6101ce10e1130e0,0x530a0530605305c530,0x5c13020530e0d10cc1,0x10a0d1060d105cd104,0xc11020d109c4306183,0x604305c4301c43060,0xc10608105cc101cc10]) else (readWords [0x23fc480cb7845bfa2,0x8a1e04c73d8113708,0x5d8158ef1090e22602,0xdc5c887112c08e2238,0x88e2258134029f023b,0xd8325d2859f446065d,0x28576447019d812002,0x35c08603afc001907c,0x8877046f6022e212f4]))
def k3 : Packing := (136,3,6,1638440,86,12,1083,fY)
def k0 (i : Nat) : Nat := (readWords [169275476,0x972c28000915083d00,0x9e0b000184b4aa0007,0xdf9a0000000103800,4434919150068,0x30452c83b410000000,0x66c401a93140358900,0x181590e60c4006e97,0x739878c268f4319a8,0xa1e8a227410f80515a,0x677800202f02991,0x5b907440e6c7f8b08b,0x68a9c416408c84be1,0xfb32f0400014320000,29,0xaa0990d58b4800e1d9,0x17e016405818117209,0x91cb65f653999ed024,0xcf0c80400004d08a6,0x610820084081054000,0x400010000a42100804])
def fX (i : Nat) : Nat := (readWords [0xa10200000e0858,0x408185082e10440a10,0xc840000161001e1,0x30a10000000000504,5385494032,0x108102819120810282,0x2820c8400001e102,0x83e0edf5ba3ccdeebb,0x539ac5dcadb68acd52,0x9f4a9dcda4f2289c3a,0x13047fbe9eaf070b71,0xaed266b2186be57aa9,0x3696439b8be50258f0,0x5a28118781e00dafe5,0xb845c530cefe1f944c,0x110aef69c91e1130af,0xb68f7360810cefe119,0x720530cef5c79460e3,0xcfb61f924c610adfe,0x9587e0d10cef5c7946,0xe10cdb655821cc10f,0x745c5315c1308fdea5,0x81205308efe91985c1,0x308fb689981cc10caf,0x619941c4308fbe8998,0x5cd108bf69a985c530,0xafa6829760a30cafe5,0xb845c530ccfe119520,0x530cdb655829c630cf,0xa609901cc10cebe539,0x260d10aebe8991e113,0xaf66809760c10cbbe,0x59825c6308fb68b916,0x1e308efe91989ce108,0xbfe999760430af3688,0x9760c10ceb651828c6,0x308efe91985ce108fb,0x6a582dc6308bfe9b98,0x5c4308bfe99985c630,0xc9f655869c430cebe1,0x39260530ad76949760,0xc108bf6a3965c430ac,0xf69491e11308f7ea58,0x320d10cfa609908c63,0xaf9a869760a30add6,0x967160430aeb692976,0xa30af96869760a308,0xef6a784a0530ceb651,0x821cc108dfe9597e05,0x30aebe919360a30ccf,0xe57845c130cee61190,0x1cc108fb6a3924c630])
def k2 : Packing := (53,4,6,0,0,9,0,fX)
def fZ (i : Nat) : Nat := 0x834601a000
def fW (i : Nat) : Nat := (readWords [0xa295fdb2e3ca307,0x852bfb65c79460e30])
def k1 : Packing := (2,5,6,0,0,3,0,fW)
def wJ : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffd8fd63,0xdda8e8aa61c90014d]),(readWords [255,0xffffffffffffd8d423,0x4082801a102900145])),((readWords [2581215,0xc636db2d3474067090]),(readWords [2171096,0x2a34960818c4045090])),((readWords [4112640,0x918c681557416c0816]),(readWords [2015488,0x818829154701680800])),((readWords [105710,0x55353e34c9ba0a86e6]),(readWords [3818,0x5424062a80ba0284c6])),((readWords [3613076,0xb48c0c06e80091ef8]),(readWords [2564372,0xb40c0c04e00091a38])),((readWords [200344,0xf28487160298718700]),(readWords [199320,0xf08487160298418600])),((readWords [255,0xffffffffffffcace0a,0x51892172a62383f801]),(readWords [708098,0xd1892132a62281a800])),(0x0,0x0),((readWords [255,0xfffffffffffffc3135,0x226350618b47fd9801]),(readWords [255,0xfffffffffffff43105,0x24250c159053c1001]))]
def wI : List ColumnInfo := readRows 27 (fun x => (readField x 0 9, ([0,8,2,1,256,32,64,4,16] : List Nat).getD (readField x 9 4) 0, readField x 13 9, ([0,48] : List Nat).getD (readField x 22 1) 0, readField x 23 4)) 38 (readWords [66160,0xac42b602445300668b,0xb869146814a09cb11,0x75b4024a1b8521d370,0x24203ad2284bc0a082,0x704c5131725383e160,0x40e5a0c80f2d05d7a0,0x2a2c401d414c2588a,0xc009d0174343a7c041,0x4530c648a300e5b4c3,0x138f610444e088a83,0x18c5112c029bac601c,0x859c03123f8401d390,0x233a9c031b5bc0216b,0xd8012d3f0205abe020])
def jB : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def vY : Nat → Packing
  | 12 => sR
  | 11 => sQ
  | 10 => sP
  | 9 => k3
  | 8 => k2
  | 7 => k1
  | _ => emptyPacking
def x4 : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 8 37 4 10 3 3 sO
  | 11 => lookupWord 48 123 4 13 6 3 sN
  | 10 => lookupWord 79 299 8 15 8 3 sM
  | 9 => lookupWord 39 99 5 13 6 3 k0
  | 8 => lookupWord 1 5 1 8 1 3 fZ
  | _ => fun _ => none
def zV : Forest := ⟨383,12,fun j => wJ[j]?.getD (0,0),wI,jB,vY,x4⟩
set_option maxHeartbeats 0 in
theorem tL : graphValid zV (boundsBefore qB) = true := checkedGeometry 3 1
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vP : block zV 12 0 1=true :=
  (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vO : block zV 11 0 6=true :=
  (checkedCells 9 0 1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vN : block zV 10 0 47=true :=
  (@block_merge zV 10 0 19 28 (@block_merge zV 10 0 6 13
  (checkedCells 8 0 1)
  (checkedCells 9 0 2))
  (checkedCells 10 0 3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uX : block zV 9 0 136=true :=
  (@block_merge zV 9 0 119 17 (@block_merge zV 9 0 111 8 (@block_merge zV 9 0 75 36 (@block_merge zV 9 0 39 36 (@block_merge zV 9 0 3 36
  (by decide +kernel)
  (checkedCells 9 0 3))
  (checkedCells 9 0 3))
  (checkedCells 9 0 3))
  (checkedCells 9 0 1))
  (checkedCells 10 0 2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uW : block zV 8 0 53=true :=
  (@block_merge zV 8 0 44 9 (@block_merge zV 8 0 36 8
  (checkedCells 8 0 3)
  (checkedCells 8 0 1))
  (checkedCells 9 0 1))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem uV : block zV 7 0 2=true :=
  (by decide +kernel)
theorem y4 : checkedTables zV 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block zV 0 0 0 = true)
  · exact (rfl : block zV 1 0 0 = true)
  · exact (rfl : block zV 2 0 0 = true)
  · exact (rfl : block zV 3 0 0 = true)
  · exact (rfl : block zV 4 0 0 = true)
  · exact (rfl : block zV 5 0 0 = true)
  · exact (rfl : block zV 6 0 0 = true)
  · exact uV
  · exact uW
  · exact uX
  · exact vN
  · exact vO
  · exact vP
def zT := extendPerm qB 13 [(383,0),(447,47),(495,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s1 : Known true zT := extend_ok (m:=383) v5
    (plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=zV) (i:=0) rfl rfl (before_sound qB v5) tL y4 (by decide +kernel))) (by decide +kernel)
theorem validF : Known false zT := known_down s1
def gT (i : Nat) : Nat := 0x1a230180fd10fc20
def gW : Packing := (2,1,2,0,0,4,0,gT)
def gU (i : Nat) : Nat := (readWords [73259428977057794,0x2082101c0c0071400])
def gS (i : Nat) : Nat := (readWords [0x613110000e3d4,0x507e48110bea9a217d,0x53082faa4885f54420])
def gV : Packing := (5,2,2,0,0,5,0,gS)
def yZ : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xfffffffffffffffc47]),0xa86),((readWords [255,0xffffffffffffffffff,0xfffffffffffffff09b]),(readWords [255,0xffffffffffffffffff,0xfffffffffffffff531])),(0x29c,0x8cc),((readWords [255,0xffffffffffffffffff,0xfffffffffffffff327]),(readWords [255,0xffffffffffffffffff,0xfffffffffffffff303])),(0xd78,0x478),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def yY : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def s4 : List (List Nat) := wH
def t3 : Nat → Packing
  | 6 => gW
  | 5 => gV
  | _ => emptyPacking
def s5 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 8 11 1 11 3 4 gU
  | _ => fun _ => none
def s3 : Forest := ⟨1055,6,fun j => yZ[j]?.getD (0,0),yY,s4,t3,s5⟩
set_option maxHeartbeats 0 in
theorem u3 : graphValid s3 (boundsBefore zT) = true := checkedGeometry 0 1
def nK : Nat := 0x110c0300c03
def nJ : Nat := 0x14090281205
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sV : CutRow s3 6 0 2 :=
  (checkedRow (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sU : CutRow s3 5 0 5 :=
  (mixedCut (pos:=nK) (neg:=nJ) (data:=fun _ => (readWords [16932,0x33220301121141340,0x101413401031423232])) rfl (by decide +kernel))
theorem jY : mixedTables s3 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty s3 0 0
  · exact mixedEmpty s3 1 0
  · exact mixedEmpty s3 2 0
  · exact mixedEmpty s3 3 0
  · exact mixedEmpty s3 4 0
  · exact sU
  · exact sV
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gN : Impossible false (graphGoal 1055) 6 (vars 1055).toFinset := plainA (q:=31) (prior:=boundsBefore zT) (before_sound zT validF) (by decide +kernel)
def jG := extendPerm zT 7 [(1567,0),(2079,5),(6687,32),(7199,61),(1703,36),(4263,33),(7847,63),(12455,9),(2361,37),(6990,38),(4963,34),(9571,35)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xB : Known false jG := extend_ok (m:=1567) validF
    (lowerFromFull (q:=1055) [2, 1, 2, 4, 1] gN
      (mixedIndex (g:=s3) (i:=0) rfl rfl (before_sound zT validF) u3 jY (by decide +kernel))) (by decide +kernel)
def zL := extendPerm jG 7 [(42527,0),(44063,5),(47647,32),(52767,128),(57887,129),(42663,36),(44711,33),(47783,64),(54951,9),(68775,130),(44345,37),(60217,131),(53070,132),(60238,133),(42851,66),(44899,34),(50019,35),(53164,67),(60332,134),(69548,135)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q1 : Known false zL := extend_ok (m:=42527) xB
    (lowerFromFull (q:=1055) [2, 1, 2, 4, 1] gN
      (mixedIndex (g:=s3) (i:=1) rfl rfl (before_sound zT validF) u3 jY (by decide +kernel))) (by decide +kernel)
def kD (i : Nat) : Nat := 0x1040a3fa21fd51
def kG : Packing := (2,1,1,0,0,3,0,kD)
def kE (i : Nat) : Nat := 0x40000
def kC (i : Nat) : Nat := 0x102de54110
def kF : Packing := (1,2,1,0,0,0,0,kC)
def v7 : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xfffffffffffffff9b5]),0xe94),((readWords [255,0xffffffffffffffffff,0xfffffffffffffff0db]),(readWords [255,0xffffffffffffffffff,0xfffffffffffffff10b])),(0x602,0xa80),(0x614,0x514),(0x0,0x0),(0x964,0x160),(0x78,0xef0),(0x0,0x0),(0x0,0x0)]
def v6 : List ColumnInfo := [(96,0,15,0,4),(1,32,78,0,4)]
def xR : List (List Nat) := [[],[32,83]]
def yS : Nat → Packing
  | 6 => kG
  | 5 => kF
  | _ => emptyPacking
def xS : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 kE
  | _ => fun _ => none
def j6 : Forest := ⟨1135,6,fun j => v7[j]?.getD (0,0),v6,xR,yS,xS⟩
set_option maxHeartbeats 0 in
theorem wK : graphValid j6 (boundsBefore zL) = true := checkedGeometry 0 0
def f4 : Nat := 0x42108300c03
def f3 : Nat := 0x68321248a2a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tQ : CutRow j6 6 0 2 :=
  (mixedCut (pos:=f4) (neg:=f3) (data:=fun _ => 0x2401212143203010) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tP : CutRow j6 5 0 1 :=
  (mixedCut (pos:=f4) (neg:=f3) (data:=fun _ => 0x24012110) rfl (by decide +kernel))
theorem j4 : mixedTables j6 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty j6 0 0
  · exact mixedEmpty j6 1 0
  · exact mixedEmpty j6 2 0
  · exact mixedEmpty j6 3 0
  · exact mixedEmpty j6 4 0
  · exact tP
  · exact tQ
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem f2 : Impossible false (graphGoal 1135) 6 (vars 1135).toFinset := plainA (q:=111) (prior:=boundsBefore zL) (before_sound zL q1) (by decide +kernel)
def qX := extendPerm zL 7 [(42683,41),(47806,42),(69498,43),(69557,44)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yL : Known false qX := extend_ok (m:=49775) q1
    (lowerFromFull (q:=1135) [2, 64, 2, 4, 1, 2] f2
      (mixedIndex (g:=j6) (i:=0) rfl rfl (before_sound zL q1) wK j4 (by decide +kernel))) (by decide +kernel)
def zM := extendPerm qX 7 [(44155,62),(44219,136),(44731,41),(52926,42),(54974,137),(42711,72),(47838,73),(52958,138),(42739,74),(44787,139),(53054,65),(60253,75),(60282,43),(44981,44),(48071,12),(53212,76),(60408,77),(69624,140)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem zC : Known false zM := extend_ok (m:=42607) yL
    (lowerFromFull (q:=1135) [2, 1, 2, 4, 1, 2] f2
      (mixedIndex (g:=j6) (i:=1) rfl rfl (before_sound zL q1) wK j4 (by decide +kernel))) (by decide +kernel)
def n0 (i : Nat) : Nat := 0x344640ac3f865fc10
def n7 : Packing := (2,1,2,0,0,4,0,n0)
def n3 (i : Nat) : Nat := (readWords [371636974411078,0xb7171000680020c000,0xf391436008009b010])
def gZ (i : Nat) : Nat := (readWords [18727267467392,0x4c8462023211880840,0x401f7cb4e4b74a0b44,0x658480fb48032fd4c4,0x10bf58032bf58c10bf,0x590109f59432be5803,0x29f59410bd58432bb5,0x8810af59010b758c10])
def n6 : Packing := (12,2,2,0,0,7,0,gZ)
def n2 (i : Nat) : Nat := (readWords [2,0x4f9400060ba8030352])
def gY (i : Nat) : Nat := (readWords [4433514884,0x210872a1e50a03e498,0x240196e52058432cea,0x62b2821b54c1610cb5,0xa98ac8086e53158810])
def n5 : Packing := (6,3,2,0,0,6,0,gY)
def n1 (i : Nat) : Nat := 0x20034000
def gX (i : Nat) : Nat := 0x3b04813058432
def n4 : Packing := (1,4,2,0,0,0,0,gX)
def u2 : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xffffffffffffff209f]),0xd8096),((readWords [255,0xffffffffffffffffff,0xfffffffffffff19c61]),(readWords [255,0xffffffffffffffffff,0xfffffffffffff03861])),(0x97be,0x2c69c),((readWords [255,0xffffffffffffffffff,0xfffffffffffff04b47]),(readWords [255,0xffffffffffffffffff,0xfffffffffffffd3903])),(0x44c78,0x24468),(0xa2f80,0x27f00),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def u1 : List ColumnInfo := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def s6 : List (List Nat) := [[],[65,50]]
def t6 : Nat → Packing
  | 7 => n7
  | 6 => n6
  | 5 => n5
  | 4 => n4
  | _ => emptyPacking
def s7 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 7 21 2 9 4 1 n3
  | 6 => lookupWord 2 9 1 8 3 1 n2
  | 5 => lookupWord 1 5 1 6 1 1 n1
  | _ => fun _ => none
def t9 : Forest := ⟨1087,7,fun j => u2[j]?.getD (0,0),u1,s6,t6,s7⟩
set_option maxHeartbeats 0 in
theorem u4 : graphValid t9 (boundsBefore zM) = true := checkedGeometry 0 0
def uK (j : Nat) : Nat := (readWords [227971182645,0x142420351320403142,0x355431423232203411,0x211512401013243543])
def qD (j : Nat) : Nat := (readWords [210990543376,0x43201024300234510,0x350210243002345103,0x402102430023451023,0x51024300234010340,0x210210341352003510,0x2103413520030210])
def rM : Nat := 0x42110c0300c03
def rL : Nat := 0x34190a81205
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem dT : CutRow t9 4 0 1 :=
  (panelDispatchBlock (pos:=rM) (neg:=rL) (kw:=uK) (panels:=qD) (data:=0x1) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem dU : CutRow t9 5 0 6 :=
  (panelDispatchBlock (pos:=rM) (neg:=rL) (kw:=uK) (panels:=qD) (data:=0x50008000607) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem dV : CutRow t9 6 0 12 :=
  (panelDispatchBlock (pos:=rM) (neg:=rL) (kw:=uK) (panels:=qD) (data:=(readWords [2051,0x20482818600838580])) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem dW : CutRow t9 7 0 2 :=
  (panelDispatchBlock (pos:=rM) (neg:=rL) (kw:=uK) (panels:=qD) (data:=0x84) rfl (by decide +kernel))
theorem jZ : mixedTables t9 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty t9 0 0
  · exact mixedEmpty t9 1 0
  · exact mixedEmpty t9 2 0
  · exact mixedEmpty t9 3 0
  · exact dT
  · exact dU
  · exact dV
  · exact dW
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem y0 : Impossible false (graphGoal 1087) 7 (vars 1087).toFinset := plainA (q:=63) (prior:=boundsBefore zM) (before_sound zM zC) (by decide +kernel)
def jT := extendPerm zM 8 [(2143,1),(2425,48)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xO : Known false jT := extend_ok (m:=6719) zC
    (lowerFromFull (q:=1087) [2, 1, 2, 4, 1, 1] y0
      (cutFromKnown zC (6688,0,6687,0,7))) (by decide +kernel)
def jC := extendPerm jT 8 [(1087,0),(2623,5),(1119,1),(6303,39),(11423,141),(6319,25),(13487,9),(1207,10),(3255,18),(1255,69),(18749,142),(11614,49),(18782,143),(18798,80),(1395,81),(18809,48),(11708,144),(3555,71)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem x7 : Known false jC := extend_ok (m:=1087) xO
    (lowerFromFull (q:=1087) [16, 4, 2, 4, 1, 1] y0
      (mixedIndex (g:=t9) (i:=0) rfl rfl (before_sound zM zC) u4 jZ (by decide +kernel))) (by decide +kernel)
def qK := extendPerm jC 8 [(2719,39),(13495,10),(3389,50),(8542,49)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem y8 : Known false qK := extend_ok (m:=11327) x7
    (lowerFromFull (q:=1087) [2, 1, 2, 16, 1, 1] y0
      (mixedIndex (g:=t9) (i:=1) rfl rfl (before_sound zM zC) u4 jZ (by decide +kernel))) (by decide +kernel)
def jH := extendPerm qK 8 [(1599,0),(12463,9),(1719,10),(2365,50),(9582,145),(4979,7)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xC : Known false jH := extend_ok (m:=1599) y8
    (lowerFromFull (q:=1087) [2, 1, 2, 4, 1, 1] y0
      (cutFromKnown zC (1568,0,1567,0,7))) (by decide +kernel)
def qW := extendPerm jH 8 [(47679,0),(44127,1),(52831,68),(42671,25),(68783,9),(47799,10),(68791,18),(44349,50),(60366,146)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yK : Known false qW := extend_ok (m:=47679) xC
    (lowerFromFull (q:=1087) [2, 4, 2, 4, 1, 1] y0
      (cutFromKnown zC (47648,0,47647,0,7))) (by decide +kernel)
def qO := extendPerm qW 8 [(42559,0),(42591,1),(47791,25),(54959,9),(42679,10),(44727,18),(60270,80),(60281,48),(69497,70),(48078,12),(69603,147)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yC : Known false qO := extend_ok (m:=42559) yK
    (lowerFromFull (q:=1087) [2, 1, 2, 4, 1, 1] y0
      (cutFromKnown zC (42528,0,42527,0,7))) (by decide +kernel)
def z9 := extendPerm qO 8 [(44719,25),(54967,10),(60239,38),(50014,49)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem zO : Known false z9 := extend_ok (m:=52799) yC
    (lowerFromFull (q:=1087) [2, 1, 8, 4, 1, 1] y0
      (cutFromKnown zC (52768,0,52767,0,7))) (by decide +kernel)
def kO (i : Nat) : Nat := (readWords [0x8151108090c8,0x8420380cd31101fd3,0xfe887f0c3f821fc20])
def kT : Packing := (5,1,3,0,0,7,0,kO)
def kQ (i : Nat) : Nat := (readWords [0x74308515c76e7700,0x818435800000a7,0x1f02000000828c06fa,0x800102590967003857,0x9507803705e0482024,0x814000001004000000])
def kN (i : Nat) : Nat := (readWords [0x1084200042100004,0x820b764a0f19283c2,0x80fe48130bf58910bf,0x58430fe54030fe4811,0xbf58930bf594209f5,0x9420bb58830bd58430])
def kS : Packing := (10,2,3,0,0,7,0,kN)
def kP (i : Nat) : Nat := (readWords [481036928000,952685821954])
def kM (i : Nat) : Nat := (readWords [16,0x4208141ba541620c36,0x698ac4186f15058430])
def kR : Packing := (3,3,3,0,0,5,0,kM)
def vB : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xfffffffffffff1880f]),(readWords [255,0xffffffffffffffffff,0xfffffffffffffe600d])),(0x0,0x0),((readWords [255,0xffffffffffffffffff,0xfffffffffffff2619f]),0x2a10e),((readWords [255,0xffffffffffffffffff,0xfffffffffffff60271]),(readWords [255,0xffffffffffffffffff,0xfffffffffffffc5851])),(0x507e6,0x187a2),(0x89c78,0x9870),(0x0,0x0),(0x87780,0xd4680),(0x0,0x0)]
def vA : List ColumnInfo := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def xV : List (List Nat) := jA
def yU : Nat → Packing
  | 7 => kT
  | 6 => kS
  | 5 => kR
  | _ => emptyPacking
def xW : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 23 29 4 12 4 4 kQ
  | 6 => lookupWord 2 11 1 10 2 4 kP
  | _ => fun _ => none
def q4 : Forest := ⟨1213,7,fun j => vB[j]?.getD (0,0),vA,xV,yU,xW⟩
set_option maxHeartbeats 0 in
theorem q2 : graphValid q4 (boundsBefore z9) = true := checkedGeometry 1 2
def f6 : Nat := 0x1408410844300c
def f5 : Nat := 0x90448d05005
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tV : CutRow q4 7 0 5 :=
  (checkedRow (checkedCells 7 0 0))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tU : CutRow q4 6 0 10 :=
  (@joinRow q4 6 0 3 7
  (checkedRow (by decide +kernel))
  (mixedCut (pos:=f6) (neg:=f5) (data:=fun _ => (readWords [37,0x234363203201322034,0x13214234010432405,0x431423402114234021])) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tT : CutRow q4 5 0 3 :=
  (mixedCut (pos:=f6) (neg:=f5) (data:=fun _ => (readWords [2368320,0x404324053241324040])) rfl (by decide +kernel))
theorem zW : mixedTables q4 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty q4 0 0
  · exact mixedEmpty q4 1 0
  · exact mixedEmpty q4 2 0
  · exact mixedEmpty q4 3 0
  · exact mixedEmpty q4 4 0
  · exact tT
  · exact tU
  · exact tV
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem wY : Impossible false (graphGoal 1213) 7 (vars 1213).toFinset := plainA (q:=189) (prior:=boundsBefore z9) (before_sound z9 zO) (by decide +kernel)
def jM := extendPerm z9 8 [(2237,0),(18109,148),(2395,82),(12774,51)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xH : Known false jM := extend_ok (m:=2237) zO
    (lowerFromFull (q:=1213) [16, 8, 4, 1, 1, 4] wY
      (mixedIndex (g:=q4) (i:=0) rfl rfl (before_sound z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def jI := extendPerm jM 8 [(1725,0),(17085,52)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xD : Known false jI := extend_ok (m:=1725) xH
    (lowerFromFull (q:=1213) [16, 8, 4, 1, 1, 4] wY
      (mixedIndex (g:=q4) (i:=1) rfl rfl (before_sound z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def jQ := extendPerm jI 8 [(2749,0),(11453,14),(1371,20),(6630,6),(13798,51)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xL : Known false jQ := extend_ok (m:=2749) xD
    (lowerFromFull (q:=1213) [32, 8, 4, 8, 1, 4] wY
      (mixedIndex (g:=q4) (i:=2) rfl rfl (before_sound z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def qQ := extendPerm jQ 8 [(43197,0),(58557,52),(64189,149),(43823,2),(46427,20),(48475,15),(49638,6),(55782,150)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yE : Known false qQ := extend_ok (m:=43197) xL
    (lowerFromFull (q:=1213) [20, 9, 4, 1, 1, 4] wY
      (mixedIndex (g:=q4) (i:=3) rfl rfl (before_sound z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def zP := extendPerm qQ 8 [(44221,0),(44733,53),(52925,14),(54973,8),(58045,52),(60207,26),(42843,20),(44379,82),(58203,3),(48102,6),(55270,51),(69606,54)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q8 : Known false zP := extend_ok (m:=44221) yE
    (lowerFromFull (q:=1213) [16, 8, 4, 1, 1, 4] wY
      (mixedIndex (g:=q4) (i:=4) rfl rfl (before_sound z9 zO) q2 zW (by decide +kernel))) (by decide +kernel)
def d8 (i : Nat) : Nat := 0x60bfd31
def d9 : Packing := (1,1,1,0,0,0,0,d8)
def vF : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xfffffffffffffffc91]),(readWords [255,0xffffffffffffffffff,0xfffffffffffffffc01])),(0xe,0x2ee),(0x0,0x0),(0x64,0x2a4),(0x72,0x152),((readWords [255,0xffffffffffffffffff,0xffffffffffffffff8d]),0x1ac),(0x16,0x110),(0x318,0x250),(0x0,0x0)]
def vE : List ColumnInfo := [(88,0,163,0,4),(8,0,243,0,7)]
def xZ : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def yW : Nat → Packing
  | 7 => d9
  | _ => emptyPacking
def t0 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def j7 : Forest := ⟨1275,7,fun j => vF[j]?.getD (0,0),vE,xZ,yW,t0⟩
set_option maxHeartbeats 0 in
theorem tN : graphValid j7 (boundsBefore zP) = true := checkedGeometry 0 1
def gR : Nat := 0x14042108443003
def gQ : Nat := 0x68325248a381a0642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tW : CutRow j7 7 0 1 :=
  (mixedCut (pos:=gR) (neg:=gQ) (data:=fun _ => 0x50634340) rfl (by decide +kernel))
theorem y6 : mixedTables j7 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty j7 0 0
  · exact mixedEmpty j7 1 0
  · exact mixedEmpty j7 2 0
  · exact mixedEmpty j7 3 0
  · exact mixedEmpty j7 4 0
  · exact mixedEmpty j7 5 0
  · exact mixedEmpty j7 6 0
  · exact tW
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gM : Impossible false (graphGoal 1275) 7 (vars 1275).toFinset := plainA (q:=251) (prior:=boundsBefore zP) (before_sound zP q8) (by decide +kernel)
def zR := extendPerm zP 8 [(59646,151),(43479,152),(55773,22),(46581,27),(58874,153)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem zH : Known false zR := extend_ok (m:=48891) q8
    (lowerFromFull (q:=1275) [2, 80, 16, 10, 1, 2, 32] gM
      (mixedIndex (g:=j7) (i:=0) rfl rfl (before_sound zP q8) tN y6 (by decide +kernel))) (by decide +kernel)
def kI (i : Nat) : Nat := 0x1948817fd30
def kL : Packing := (1,1,3,0,0,0,0,kI)
def kJ (i : Nat) : Nat := 0x8e80
def kH (i : Nat) : Nat := (readWords [616720676,0x3a037eb0261df54530])
def kK : Packing := (2,2,3,0,0,5,0,kH)
def v9 : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xffffffffffffff22a7]),(readWords [255,0xffffffffffffffffff,0xffffffffffffffa027])),((readWords [255,0xffffffffffffffffff,0xffffffffffffff4759]),0x4258),(0x942e,0x8424),((readWords [255,0xffffffffffffffffff,0xffffffffffffff99d3]),(readWords [255,0xffffffffffffffffff,0xffffffffffffff3bd3])),(0x81c,0x4408),(0x21a0,0x5f80),(0x41c0,0xbd80),(0x0,0x0),(0x0,0x0)]
def v8 : List ColumnInfo := [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def xT : List (List Nat) := [[],[16,66,101]]
def yT : Nat → Packing
  | 8 => kL
  | 7 => kK
  | _ => emptyPacking
def xU : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 1 6 1 1 kJ
  | _ => fun _ => none
def qG : Forest := ⟨1151,8,fun j => v9[j]?.getD (0,0),v8,xT,yT,xU⟩
set_option maxHeartbeats 0 in
theorem tM : graphValid qG (boundsBefore zR) = true := checkedGeometry 1 0
def gP : Nat := 0x10842110c0300c03
def gO : Nat := 0xe86824914642a
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tS : CutRow qG 8 0 1 :=
  (checkedRow (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tR : CutRow qG 7 0 2 :=
  (mixedCut (pos:=gP) (neg:=gO) (data:=fun _ => 0x2615312126154121) rfl (by decide +kernel))
theorem y5 : mixedTables qG 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty qG 0 0
  · exact mixedEmpty qG 1 0
  · exact mixedEmpty qG 2 0
  · exact mixedEmpty qG 3 0
  · exact mixedEmpty qG 4 0
  · exact mixedEmpty qG 5 0
  · exact mixedEmpty qG 6 0
  · exact tR
  · exact tS
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem jW : Impossible false (graphGoal 1151) 8 (vars 1151).toFinset := plainA (q:=127) (prior:=boundsBefore zR) (before_sound zR zH) (by decide +kernel)
def jL := extendPerm zR 9 [(2429,28),(7038,16),(9598,21)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xG : Known false jL := extend_ok (m:=2175) zH
    (lowerFromFull (q:=1151) [2, 1, 2, 4, 1, 1, 2] jW
      (cutFromKnown zH (2080,0,2143,0,8))) (by decide +kernel)
def jD := extendPerm jL 9 [(18814,16),(11742,83)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem x8 : Known false jD := extend_ok (m:=1151) xG
    (lowerFromFull (q:=1151) [16, 4, 2, 4, 1, 1, 2] jW
      (cutFromKnown zH (1056,0,1119,0,8))) (by decide +kernel)
def qY := extendPerm jD 9 [(44925,28),(50046,16)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yM : Known false qY := extend_ok (m:=52863) x8
    (lowerFromFull (q:=1151) [2, 1, 8, 4, 1, 1, 2] jW
      (cutFromKnown zH (52768,0,52831,0,8))) (by decide +kernel)
def qT := extendPerm qY 9 [(44159,0),(47743,1),(69501,84),(74110,21),(48094,83)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yH : Known false qT := extend_ok (m:=44159) yM
    (lowerFromFull (q:=1151) [16, 1, 2, 4, 1, 1, 2] jW
      (cutFromKnown zH (44064,0,44127,0,8))) (by decide +kernel)
def qR := extendPerm qT 9 [(43647,0),(46455,81),(51063,154),(43901,28),(46461,84),(48510,16),(51070,21),(43423,155),(58811,156),(59900,157)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yF : Known false qR := extend_ok (m:=43647) yH
    (lowerFromFull (q:=1151) [10, 1, 2, 5, 1, 1, 2] jW
      (mixedIndex (g:=qG) (i:=0) rfl rfl (before_sound zR zH) tM y5 (by decide +kernel))) (by decide +kernel)
def z3 := extendPerm qR 9 [(42623,0),(60285,28),(60286,16)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z4 : Known false z3 := extend_ok (m:=42623) yF
    (lowerFromFull (q:=1151) [2, 1, 2, 4, 1, 1, 2] jW
      (cutFromKnown zH (42528,0,42591,0,8))) (by decide +kernel)
def sW (i : Nat) : Nat := (readWords [0x28270019312920,0xf8e91910020841c006,0x2403e3031e1d18e0d,0x8d0c8c0b8b0a888028,0x504c483c3844400101,0xe1c1a180e0060b0a09,0x80700303028201810,0x801fbb98bdd7a82ec,0x539c87a00ff503fd43,0xff54ffd10ff083fc40,0xff0c3fc53ff18ffc31])
def sY : Packing := (10,1,7,0,0,9,0,sW)
def sX (i : Nat) : Nat := (readWords [10,0x49b3289cfee0003c11,0xe62e10c1e400023500,0x513996000090c91cf,0xa000013a78dac3f26,0xc00039c5cb80000000,0x204a000000452c00,0x1633e0e551fc80b152,0xf0f95a89a255e23881,0xa8be81b938018248c6,0x65c070000000000b3b,0xc9a800000031700028,0xc3072b06ecfafc9837,0x5010470c01e16716e0,0x74d6b0bf948ee3ac96,0x36e0054814054a5,0xd5892c4d40b354401d,0x8907a8d08616748686,0x6b2610135be1dd1165,0x170cee09f0f01bcb5,0x800000010d202243f3,0x18eef1419c646e0a9a,0x79430db52928c52c,0x5193c564cb39a69000,0x28ec00122803750628,0x65214c24898f806a2a,0x5df5d43e1d42ba11a4,0xfe586827629805dd99,0x2be81c8003761a6d0e,0xc800000000072b8000,0xc8986beae000000185,0x81727cae660c120006,0x8bc0011c561f014800,0xb8c0000001cb4c5e7,0x11000138985d121316,0xf8741ed00000000000,0x907402000000,0x4d29b7e000c0d67181,0x8d8a3e1049165c75b6,0x93b0000000c7511c31,0x3d41fc131606bb107a,0xd0436070133001020,0x700000300000004610,0x6da15030000002,0x500000000021061070,0x3013010000000a0,0x20130090060020020,0x100100240030000015,72075186761310209,0x10001104000000010,0x400000000001011])
def kY (j : Nat) : Nat := (if j<1 then (readWords [0x4670b12533d10c,0x75e8c8b58478714c78,0x518d7ffe317a00012a,0x9ac91478d191b210c3,0x2553e54c93f8948122,0x4ccae8c8db6fde2547,0x91fe4e848fbc887bfd,0x7bf91489036fde2547,0xdcf8012e849566e24b,0x9fb14c8811a0e059e3,0x52b5153447cbd4232d,0x7f49221033d2726414,0x7a231b409789c248c,0x37effc18880013340f,0x91678851c118ebe79,0xab9993d531d8dc499a,0x5bd0c116be4b20866,0xcfc8181973f508195b,0xdbb50994f7c60a504f,0xc8428b9e9121c0ac4,0xfc46a1120e04a60f44,0x53fb885004944e5f86,0x55bc6ff42c412779,0x9d428024a1e7ce7ac1,0x704adc7e20451ffc42,0x44651f5f0228486f4f,0xa1954c1e8977ea4a0,0x53be12443c9c3c6580,0x589afe03afe94c9448,0x9efffa830090fdb8d0,0x417f449000ce5f928a,0x32dffc2d0614d27f80,0x7b0a67cf1f4d91f647,0xd4208fbfe370010109,0x6bf0781268499f1f02,0x903ffe01040482f,0xca44652ffe289a4fc1,0x22aff8d4941804bdf2,0x3604101297c7e21401,0x24af7ee811a7f86101,0x1d78f7002c80953e38,0x1127d8e0211e7f2991,0x42fbf18650920df8cb,0x8019cf270f30e05479,0x38798702a5ebf90311,0x20250f9f5818890128,0xf270f30e05400fe351,0xd6404a258208d1b924,0x507a3c1d8e86f1d841,0x349848218d86b12821,0x2494478f110820c0a8,0xe62006815047c23094,0x8a42161f9088a0318c,0x9c0a1707c9404221c0,0xc881288b0503b15130,0xa240108fc04381b1a0,0x844030838cc0801088,0xb84e07148944900150,0xb4582b1787c010b284,0x6416a08101e7fcbfa1,0xf92fab7c5bddde64f0,0xb778bb55d82e9e73db,0x929c58e0c6f43739b5,0xad886b9b591a7ed1d6,0x8533b5996cb263d319,0x988cc2b606af8d78ab,0xa05bcad9566ab10570,0xab25534a8d52fa8ed4,0x1e9ef4eba72935296e,0x4a92505254906477a3,0x591928ae444219908c,0x8224009f80f6c78e3c,0x9da0e727113711ad0,0xd0066031e1840bdc5d,0x52d89660ad254f2941,0x3e49b64b1247919c87,0xc4161f88ef47203651,0x9c0c605f42df15609f,0x849e22e105076437c1,0x9a0bf054424c0f9066,0x25c0c403500052411,0x4a83d264f4b885240f,0x4b93d2a234983d2a4f,0x4bb3d2e6f4b24d2813,0x498352c034b1852c6d,0x4902d242d4b9352409,0x4884d284d4aa3d2633,0x4a0bd2a614b0bd2c13,0x498852eaf490352c73,0x4b1bd2a274b13d0e4f,0x4b01d24134a13d2403,0x499352e334b09d2407,0x498b522014a8c52e2f,0x4b08d2c114a84d2613,0x4ba4d2e8d4aa352833,0x4b9b52e61498052c05,0x4384d0e4d4a0352a43,0x4a9152a474b84d282d,0x4a8bd2c0f498bd2401,0x4a002ae4cab8c32846,0xeb1caae10ab883282e,0xab84aae22a393ca40c,0xabb0c282cab91aae4a,0xa3932ae0aab8caae2a,0xab982aea4abb128e13,0x2983aaea6ab913a610,0xab8a3a612aba32ae6c,0xabb1aae26abac2ae4e,0xab822ae42caa3aaea2,0xababaae048b8a1ae46,0x2ba9a2e260bb192e66,0xbb0ffffdfdfbfbeff,0x7dbdddebf3f54d4350,0x11018c53100310c020]) else (readWords [744459458756178,0x268663fe3f325000b1,0x3ca8643f53090a16b2,0xb1c08e6b231fc5008b,0x7c382938e31a32317b,0x310ffc6068f4091041,0x3efe1f6c01485ee44d,0x9b654c87a249bf13a0,0x91bbf9e4f32ae0e4e3,0xd3a92ab09fe26af3c9,0xe651e04e8247ae7089,0xa62f4408edf4ca4466,0x3e5120b04991818324]))
def d7 : Packing := (122,2,7,720906,68,13,1115,kY)
def d2 (i : Nat) : Nat := (if i<1 then (readWords [0x8d2114ec42d555,0x274bd2a00000161bc6,0x98a2be56e421c83e4e,0xb400028745174e28a0,677789873,0x403000000000000000,0x29000001258a89ff00,0x992fe0002b3da039c6,0x1254b5a7f81c0000a,0x2dd89140da00006de2,0xa4c59326092843a174,0x50c9f98641eb8a6b0f,0x32194d57899800010,0xe20001c2208b800000,0x2805000000000000,0x585b4e2b828d9a9,0xb073f668000000008c,0xd0000ca8dc8ad2baca,0x4800000006ec300006,0xefc281810153c0000,0x217ef0d083fe87f,1794088372097,0xec09a000246b324e00,0xa18c000390100014,0x15c9baeb4c41fa9478,75091250574426123,0x516940168a70089713,0xc725c00019a69eb0a0,0xe0430e88f585868e06,0x60223a8000a20e09dc,0x8435154e1a3a209844,0x215f52428c1cc67013,0x432ca00034b5802270,0xffe195659f02531b06,0x4907608000e55761ca,0x5e994bc50c000024e,0x80003a02817f18688f,0x76221a3d7d8af0df90,0xeba87909b1876f302c,0x105aa7800000000000,0x60c0e190431ed5c,0x5ec7000063d08b7742,0x86a09c1800006874a1,0xac3148761ac934514,0x90187128de904f0308,0x4bb0000a1760000000,0x300806afc2d7193f6f,0xb0001841047b129960,0x5400e8ea3fab29decc,0x4b4cb3f14996518be8,0x37c8c662106570000,0x523a41e200014bda0c,0xb8046d9e082a6aa400,0x259c4890f3613a2,0x27b440214710bd222c,0xc55f95a52ee000384b,0x99090001f43ac0db05,0xdc2c380b606a4018e2,0xc7c29000020e0b2c1c,0x36d592581d405720e2,0x70800051e58148179,0xe57ec06e29fd94ff15,0x96e576499887e93d52,0x40000000000000000,0x795500018280,0x403f0001612c000,0xd1780598000000,0x115f98a2c6b800031,0x1dd8c356120d5b0c30,0x3bf0199866f08fe41a,0x48e86705255e23385c,0x8000b199fa7000050b,0xf517da340801104c12,0xde04508900000b134e,0x67c961c1421cdc609,0x488c1179277c579c8b,0x767531636558089d34,0x7628365a2ca9e67f39,0xdc94eff59cd5e90d48,0x1580b63f30a091557c,0x1e97ce0ab2092d9b,0x9923c13184648424ae,0x92a2000251800e365,0xb6ec4f892fb1b00c5d,0xc12c482812e2f0e3ac,0xdd56a4e1cbc,0xe14af06045e8559b82,0x2a28aa3599f78a280,0x94d6254a491b0a46e,0x5c4126684e456a0000,0xc079b020000034f4b9,0x50b30000428604a800,5105464176577024,331488,0x255e0000d1f60003,0x4aeaabb506cd2c0000,0x502a8681003000e00,0x140330401a0204c8b1,0xa00001810408004561,0x400304416020230110,0x24280ba0254000865c,0x1840010380140418f1,0xc0150e04008001d0,0x71a10080281008102,0x181030000081320400,0x4060008e000c00e000,0xc78710080080004291,0x40029d2a44b060000,0x6020a0048206000030,0x2c0042e002800c180,0x8804104021e0c18108,0x40800004400060008,0x818243810040104020,0x81091e001882208203]) else (readWords [6986,0x50500001d9fb975a15,0xd240d09f665ca19400,0x10148000d11204700,0x302ea103812ad928,0x41b8000000718e4,0x169580000000ec7,0xa54fe07d532f9ea600,441991382612288,0x5ceede82b68ac1,0x14331d200000002c30,0x9023e0d6a8e255930f,0x60000c3e4692000000,845286578585624,0xb2000032dae49dca32,0x8dd0000a33c802b87e,2207689202831,0x5b1242c8cbf3068ec,0xc87758a5e2ae00033,0xb16092dd50a395c365,0x6b110702c1017c118,0xae2964af86cfc21792,0x48c7f843873f929c84,0x3749a8d53e0a64b791,0x7a78aa300f619f11a0,0xa6c8001a2da47e4e38,0xc952035c3c914c125,0xe79dcb032d7fa52532,0xf204a38c452e64523c,0x2d6831f0269d1e3b60,0x46b502a1432594f,0x8042e11bfb57140000,0xa50987ce83cb1f000,0x31980004d6a00010,0x94d53200010bf80001,0x6ed000074c40006015,2316732203008,0xa15c1ea832e2e163,0x9ec13384f000000004,0x985c7752fb3484c946,0x32b82150298cb54f67,8661277,0xa000200d009f000000,0x10a20000000144eac,0x4c90ba0127cce6836c,0xb09b02f9c9c5737045,0x411fc4dc83c5131302,0x9e144400d939d939a2,0x6f84e6069a63962ca0,0x54f61f393ca2d000fd]))
def kX (j : Nat) : Nat := (if j<1 then (readWords [0x6525d9a24904d8,0x9415292e2f4660a546,0xa02949804e92e60125,0x80e3841401982aa92a,0x4d525c84a4901d4960,0x28e285512442340a12,0x9793064f2c6e9261e3,0xaea93e49204ef2a521,0x754a9a4b94249760e9,0x2407125d43a4bb2b51,0x60ad12a2b066119c4a,0x8b94954511aa4e1c50,0x8d249035714182e282,0xf524812a4b9398d206,0x8910f412482ca4b09d,0x49727c92a44de58dc4,0x4409749204d1ac0e12,0x5825c4b0d4714236e2,0xa8d866008a4c28e793,0x17092e42925d820cc2,0xb55d52a91ac2e1e4c2,0xa24ba8349730292e8c,0xd25d4224a8b6496366,0x330539261d244a8ad8,0xd845292e6cd248118c,0xc2b4198224a2c03125,0xca7c6900b49406692e,0x4f622063a4b9544982,0x44330ce125465bc982,0xc4971871a60a52614a,0x24a0598d2071110341,0xe4c27a4b0351983511,0x102dc6619a3cb1d449,0x76583306a525c8424b,0x88279537092407dc55,0x1724b0cb19855e92e4,0x2dc502a46c1a98d203,0x4f2615d2614e82c122,0x487860b0e18161e18,0x2c33629523e090efd5,0x551e8243be05821e0b,0x6a0e5cc30243d7595,0x2a27ac274e480f36aa,0x380580b20b0ec98212,0x890b09039730a23075,0x4e20e282c14d058366,0x82c270d50a6b4a0c20,0x581408a4094160a314,0xa94d05870a43024085,0x85002c22821602c0b0,0xad8e4c260ac0b10580,0x2ceaa6e1048119ec01,0xd05823e53047ca5487,0x8243b94572707b0a74,0x858081c985904879e7,0xac0741604f9ca89e3d,0x72328ae6a5b505c02c,0x3ba40818a52c27ce54,0x8f02c14e21524042c0,0x801605b20a0a861429,0x52a538121e81aa120,0x5849c130d38121d91,0xaa11c4d63aaaaa5001,0x6013bea12935423eea,0xc6e1654ab34a0ae215,0x14082a2d0a480fba98,0x504171307ae429a505,0xc9cb1d805859882c07,0x1606702c3835954ac,0x52a23c848081cb09e0,0x5818c6ae500e580f20,0xb8830487a6824070e4,0xc268243ad41863882a,0x471358ebb4a12f5554,0xa70a82a41604810c0a,0x5822a0b0ef0d5c9d,0xb2a117418538090ec0,0x854483a90480487845,0x2a27c360600243b121,0x204042a441d4c5c20b,0x88929813e72e60ca58,0xf9ea89d29522a8a40,0x881604796a11e1d424,0x30d389508f98a11c,0xffbfdff3fbfebf7fdb,0xeffbbedfafe7f7fd7f,0x3fbfedf7fdfb7ddef7,0x7dbf6dd9f5fd3f3fcb,0xeffbf6f7bbebf9fe3f,0x5c5535c1535915358d,0x535815350553501534,0xc5534c153481534415,0x31c1535d5435c5435c,0x14358143545434c143,0x481435d5405c94058d,0x405894058540581405,0x514054940545405414,0x50940505404c9404c,0x5404c140481401c940,0x5d1105cd105c91058d,0x105511050910505105,0x1104c9104c5104c11,0x48510481101c9105c,0x8635c4635c06348063,0x5c4535c053480535d8,0x405d4405cc405c8405,0xc44058440580405484,0x54440480405d8315d,0x4315c8315c03158031,0x548315d8305d4305c8,0x305c43058430580305,0x483054430480305cc2,0x58c2054c20500204c,0x4204c0204802044020]) else (if j<2 then (readWords [0x91681d011002a0,0xfd070f4380c4270111,0xf8940107c110cc0787,0xd000a6000b8000b02b,0xbc2deb07517a69d25,0xe8cf4179efcdae64f2,0xcf94fc90e4271bb8b3,0xc3fe1870a3833c0bdf,0xe6fc77c5bd4ddceeb7,0x743b8ddc2ede76c1b4,0xbd966c7761faf6d6ce,0xb0f569a9fd4aea174f,0x7a6ad2de93b47ba2fd,0x10e8273fb9e3ce566b,0x3333987cbc65b32bb9,0x4cc9c64b72258fac6f,0xe34f1898b1c4f625b1,0x1868c27e10b06d81f,0xc065fdefc77d5be45e,0xcaf3178dbbcddaeebb,0x73eb925c2edf36ecb7,0xdb42d836b3b53da62,0xcff673b2ed93ac8962,0xfb0ad80ebe75dbae75,0x6d2b41595abed5d6ad,0xb553a9dd482a0b4eea,0x6552be94f491a3cd19,0xa883430a12503e8013,0xf39f44f627953ac9ca,0xce1a6f135a99fccce6,0x3b30d97a4b9a5a52c2,0x9554a7650f27d934c9,0x7a49923a912c862405,0x1e38e3c6ba34518e8c,0x2c5b22b514289d4482,0x20b0f486b43261830a,0xe84b421e0e506282b4,0x10e06701d807400dff,0x6fee7f03f55f8efb77,0xd5be7df2af827b83d8,0x9e9af367943c55e14e,0xfc7773b51d8ceb9751,0x3a4dcfce7272f3941c,0x8ae39711b855c12df2,0x6f5377dba2dc56dd36,0x89b18d776b5b579aa4,0xd4769a34a1a2cd0a67,0x933999a4cb6655b271,0x90ec6c62f312186cc1,0x86052ffd7cebd25e12,0xec5740b8d5b62d3566,0xab28586ac0d5e8ae45,0x6a2af5556a9a53ca98,0xd480a26503a7cd3cc9,0xda4e026c534c98c4bf,0x25b92b894749ea4892,0x68ee46a231d1688a7,0x44821d90cc85341c20,0x910207f43ef1f1cf5e,0x79b3bd1d80e8c73839,0x1c34df46db3659ad0,0xd3869033f19acc9463,0x7311981cbe85d42dc1,0x6b8b445922be1574aa,0x654229a9450a024ee2,0x6992dc94e494242117,0xc87c42e2098fe07c43,0xcf1d20e507043611a3,0x8ce864e31c1830bb05,0xa42bd1508a0c4e425e,0x12788fc45621210107,0x9c3a21b20d206342f8,0x1680aa84d424a10b07,0x9839016c08e03080cc,0x33031d25c9fc4b0,0xbb71429292e21a3481,0x924c3a1198262a2c11,0x1261e824b88549208c,0x92ead525c6ba4904c7,0x1425e92403d2618e38,0xa1188d20aa93049634,0x81aa490228d2062f26,0x142254578cc3361980,0x86910518660670cc32,0xc71422ef2415925c8c,0xcc10c492096f24121,0x248104440a45161831,0xa413d2486324bb038d,0x4253110284660d9a4b,0x881498366330269c54,0x9dc4a8d249765a92e2,0x2925cd48cc22971418,0x712a2ac6605224b09f,0x493066baa501e4c24a,0x4b94171423292c0746,0x6050a4b013893154e2,0x84c62204438a0c4495,0x29692e4dd25d5a0cc2,0xb689525ee240edc551,0xca4bb2e1980191a412,0x9754a4a4ba8289515d,0x1a41046608da4b88b4,0x920b092e22125ca224,0xa9b35d529f12a20e25,0x59bc9932198074930,0xc4de4c5d46a8b84970,0x9e3305246601946902,0xd49765e92e4312548a,0x28b09a796090330125,0x25cd50cc2ba89516a9,0x2e46521ca324c30d49,0x202092c13125d81389,0x4081207e330311254,0x9a44408189516892e2]) else (readWords [0x340a25a5322c508,0xf112816314116c3de5,0x4064dca108c686c049,0xec18d808de0829e121,0xcf18c88708802c913c,0x53686908722a6065d,0x5041b011814e221803,0x127c898cde1045fae,0x190e111e05df2863e,0xf912326700c7468777,0x88680cc210053a42a3,0x435615f2106c359147,0xa03199093c85065f40,0x630ff70992f091d6cc,0x53108c84e116c50b54,0x50d0144be0640f4a63,0xc9700c86421c8b2da1,0xd9923005f190e3e018,0xddc2106b41602dfc08,0x67848d7a886ba88759,0x1588b5e282f71020d8,0xad4a19e0559147cba,0x6417d1a0f6f8489bc,0x215585808f90aad09a,0x45a83b90a7f0488c04,0x6f0415a234057a887d,0xfd531a78c4bc06dec8,0xc6e021b3e9127810e9,0x87b431800047f00c7,0xde40c60f0020f47e82,0x20fd0436fdb422651f,0x810880159731d7a031,0xd65625ffab00233cc0,0xd8084f486748b68240,0x9780cb036fe60190bc,0x319c22c6073a78064,0x8790506c05730922f2,0x153c2a0cb619e04319,0x42af60636810f58860,0x12d7219028958b7842,0x1d6a1d5867f443cfe0,0xc8bfd44885f4a633,0x2cf06200c7ca18cf2,0x238fe26300e70020d7,0xd79221ec0f3a780645,0x81005af232f2863a70,0x3ba14336236020e0c4,0xc7433e221eb8140400,0xd02388980dc4506846,0x4c040147262de108b,0x61677416403630d86e,0xb91d21ac8ab222fc89,0x8de02581278463a343,0x3d243d41da143b88a9,0x981133c492c0a8147,0x286300a43ec0a81521,0xcf6663e2e18d7c486a,0x5b415026026708d80,0xbb262602ef80636021,0x3a43af362642048e06,0xe1848ef10a0ee22a4c,0x495ba625fd08115503,0x40590e2c735843be22,0x3b11e6989f6022fe81,0x118edf1613b79231b,0xefcc312a023810f8,0x88f88a78e219c84766,0x235fd020232f848796,0xc3d05967c0844edb49,0x8cb6e848c034039f02,0x1107021024fc218de0,0x29a42be08e62a86016,0xd509453b7c584f3584,0x3ce68191c057109120,0x798c18cbf80639a424,0xecc590e8190cb090cb,0x923c10193b3263ce4,0x8c75e24c72c904bfa0,0x4046ce68192fc40267,0x8083e018ee2121fa23,0xfe404c97845b65511,0xbc218cc0b78424ecc4,0x9dbe08655bc09b5086,0x3c8508bd0d8b035c91,0x977fa0910023023e03,0xada98cedf16138047e,0x370147d309195f602,0x1f023c8740c85fa44c,0x97c44fb010b8133ca8,0x100ccbfa0404698428,0xf448c990e81917c243,0x4ecc45fb1482819e69,0xad5245fd020236734,0xc96223e446808af92,0x49f021127c08449ac2,0x1d72923227ca48c8bc,0x4232c24ac467c0679c,0x46be80443e039f5a08,0x9b2b221f790c26780b,0x3a1319b810cb092f91,0x187e1d0321f01b7ec0,0xc7b59288708829e5ff,0x3e22a9c6fd08248df7,0xfcca0824053cbfe7c4,0x54be30c6f1a092a210,0x88340e91013c280584,0x1913414844b4961d80,0x42140842076168d112,0x8a0020412308300422,0x41c581bc54308404e0,0x71228552789d4186d1,0x54a02409604480450c])))
def d6 : Packing := (387,3,7,2359386,103,13,1105,kX)
def d1 (i : Nat) : Nat := (readWords [0x4048000b050c19000,0x427c0b6c0ae0f8000,73446353935101989,0x4c0002c1800020759,0x179d2161bfc05f1f9c,0x566d19c76b1d2c3080,0xd1a07c04df1a000000,0x3098000c08207790b,0xc000d109d3bd0a6807,0x18000312ec6ee1e6,0x3900c583a64be4353,0x18e5361509868521b4,0x80d14000061f544fe9,0xa2085606fc21202242,0x2905f08741ac000000,0x3c0b40dd01e10ec840,0x11cbc52b0e0f51a123,0x465808c85a1c044466,0xf4c1561b5c0ce4440,0x812a82800f105b00,0x286710ca054a1b085,0x800014600000000307,0xc483404304d4074c33,0xc1ff0841038,0x484ec36f1c287a8,0x1ef449f20986a315ec,0x62200000070b948101,0xa6f5f2222844000041,0xc0000000500a40d000,0x2025706b864214c000,0x2043000145c203f,0x51d0003c61000342b2,0x11600150a800000000,0x11e000081cc00059,0xff03f0001b45b17c01,0x611c5424e00c00014d,0xc05d0000b5a6c44441,0x44b2c2c0147c7cb044,0x7013866515700a4,0x4048b3520eb08aa56,0x95d0a7551014001041,0x10500d38b50100a080])
def kW (j : Nat) : Nat := (if j<1 then (readWords [0xcf10e13bf579ae,0xc5c2b756a2cd588b01,0x5e2b6560ab1536a0d3,0x9a634a690d19a21422,0x804f49c9362684c397,0x72ce52c8d8f91d2364,0x5c8a911e1d42e84d06,0x608c057f4fc9f53da7,0xa4f1ddfbb775ee8dca,0xb8d6f6dadb1b4f684c,0xdd9331961ac05792e6,0x5acb0d5baaf538a293,0xf2744d09812aa46476,0x8bd13a0d40a7d4ef1c,0xf38e6fcd91a933863c,0xc39772de570aa14226,0x84908e10b1f43c86f8,0xd71922d85309b12421,0x83e8710d0170268420,0x660940d00f00013309,0x42649c6ca0b0c54187,0x4ac3246645536a9478,0x5422c1330a026430ea,0x90069c914e9a40da95,0x64209034752033292,0x241b508ce49842a963,0x7a7930252481b8cc8a,0x5119128790335f5089,0x6c899c930be52a544,0xf206b8ccc250991c3b,0xa413cf245206c91ad9,0x417cfa844e250869e4,0xa6d94158510f54e21,0xec0ccba19d60121131,0x8dc244b7098566d423,0x52a54195806b2b08b,0x85421213235e250829,0xe48a91995011284334,0x50821443dd6d4238c9,0x2274264a284c9533c9,0x84a1324d21480f4e48,0xa38d510312e219f508,0x8c4a0b128878cb2847,0x5b508dbea114516132,0x7ae22275457b6ba871,0x5911d324039c545ccc,0x903919921b12c31365,0x5704c95c6d422e2b2,0x43cf545598a11b7d73,0xfaa40d46644588c91,0x5454195192245b508b,0x70984189710e2b303d,0x9244164a0bfe52066b,0xac251858471e40a230,0x876ab2847cf206cc89,0x857b154787b0eea250,0x8518aa408942123930,0xb784c26489014b952a,0x942c983348192aa11d,0xbd209c01300c126129,0xa952b520b60130809,0x21f134a116348396f2,0x84470505d9643daad3,0xbd028427fc7f4fe5f,0xb3f57e9fd1f9bf2fe4,0xfc5f6be97cef8dedbd,0x6f87ef9debbcf76eeb,0xdb7b5f69ecfd8faf75,0xde9fd2f9ef3be6fcbf,0x95f1fdf9beb76e7ecf,0xb9df3ae6fccf97f1be,0x1fbf95f6bdd77abf1f,0xe3ec3f4817154d6359,0x15321d6454d5458d53,0x5014154d5450153549,0x4054c8750153549305,0x4c844c15361d2054d3,0x4815321d2054c8148,0x1535491054d2044153,0x21d1054d861c153610,0x7054d811c153549305,0xd424c14361d2050c8,0x148143205725018158,0xd40505625016158140,0x5c954501525454021d,0x5150172505404c5325,0x1544c540545315008,0x74c54058d30501614c,0x14058130501524c140,0x4c5305008148140549,0x734408758d10609544,0x418155110509544408,0x755110549414414250,0x5105d9404418448110,0x5cd204414248110505,0x20441404811060c724,0x41541c9106017218d2,0x5c4634817018d8748,0x634817114d825c053,0x4817014d8748053205,0x2014d525d840545761,0x1425d840481761018,0x25d44060575101615d,0x44058175101525d440,0x54575101205d440585,0x73101605cc40549731,0x1515cc40481731018,0x5c84058572101605c,0x84061971101855c440,0x58171101525c440481,0x711018258440509611,0x142580405c5511008,0x148040549760c1205d,0x8305cd31081714c420]) else (readWords [2782270,0x6105ac2095c0d7b8c6,0xc040101078c50c0aaf,0x41113c18a9815e610c,0x3b2626c097a420000,0xb21321002046420000,1099516879842,0x2502001a0800026c21,0x860c6f60300003e220,0x701380b5040168201,0x6424080000f8880180,0x8000004a0c3020152b,0x14d210007831458481,0x2e909c056432837488,0xc866108be314a08007,0x3625f90ac8501b2100,0x205748980990802c7a,0x4880134853f090ee91,0x548802e0270100,0x4e210003762005e909,0x3613e2200dd2168d08,0x34c218058442710ce,0xc0e90804c8402c0401,0x6023244c04c9126074,0x8690992206610100a2,0x784ed04271200030d0,0x19507a0004620e00c8,0x30008f90124ec020b0,0x4a828120fd1662d45,0x48002c43e0b8000290,0x5e0ad0002dd73ac74e,0x689ced99f28e46c7d8]))
def d5 : Packing := (137,4,7,3801188,103,11,1064,kW)
def d0 (i : Nat) : Nat := (readWords [0x247800a1c000850,0xa0de22d610c00000,0x272000f1bc2ec1b907,0x25c1d40191e0508b44,0xd01001a1400000c080,1115951632])
def kV (i : Nat) : Nat := (readWords [48413249110244,0x10815871042002c080,0x3504205c102f02,0xd800181687ab67230e,0xfab6722e19d5c1ad99,0x85712ce84403d49524,0xc087481538fc2a5206,0x5544430dd63640875,0x9153de850898505204,0x43f40a1481524c153f,0x6848171509601039a9,0x2021d4255110f4a481,0x4258175103d2542245,0x205d4409dc69498505,0x20443d8542245205cc,0x40fe0509302052050f,0x9a542261205c440f29,0x50891481761039d130,0x2048748153f6250920,0x58173103d615148152,0x5cd10b0729d6455163,0x54e07ca9549861c153])
def d4 : Packing := (19,5,7,0,0,8,0,kV)
def kZ (i : Nat) : Nat := 0x81900
def kU (i : Nat) : Nat := (readWords [163,0x390a134a4c28290221,0xe50549302048748153])
def d3 : Packing := (2,6,7,0,0,3,0,kU)
def vD : Array (Bits × Bits) := #[(0x9017721c30,0x14b5bd0008),(0x500e080936,0x634240ff36),((readWords [255,0xffffffffffffffffff,0xffffffff4ca8886101]),(readWords [255,0xffffffffffffffffff,0xffffffff8c0d9a00c9])),(0xdc001a04a,0x12b065ab12),((readWords [255,0xffffffffffffffffff,0xffffffff815101844f]),(readWords [255,0xffffffffffffffffff,0xffffffffe94a0254e5])),(0x2200761284,0xca4842b0f4),(0x0,0x0),((readWords [255,0xffffffffffffffffff,0xffffffff2220844287]),0x31b2254f02),(0x0,0x0)]
def vC : List ColumnInfo := readRows 39 (fun x => (readField x 0 17, ([0,16,32,128,8] : List Nat).getD (readField x 17 3) 0, readField x 20 17, 0, ([7,8,4] : List Nat).getD (readField x 37 2) 0)) 80 (readWords [8389472,0x14900074002890c4f,0x80c10204b700408800,0x4e001302baec2b8105,0xd0f85d50218af01810,0x4087e009000429c040,0x62000b8005420cb700,0xc084695e068203387c,0x33a81054f805104003,0x9000861ad7c1ac02b3,0xaf43380a00528000d2,0x2c9f02c202194e2183,0xc29c0c0600f5380f,0xc40087000385f57a1,0xf404c32dc430211a5b,0x81a040acbb0ac04801,0x620001d00298000645,0xd5f05d008a6bb0a604,0x80147000290006d800,0x92000f20040c00ac00,0x138014c40012002ec,81070153413012171,0xd0ac021583e1594035,0xa9c358605d5385d0c0,0xaea70ae185c57a1c40,0x43887c38a81725e872,0x10a61f0a6a014d4e1,0x4c300187c01a800353,0x8030c30caf10c105ad,0x5e1ac20aeabc2e8415,0x757857082a6af0a610,0x4615e0602082af4028,0x9051f805402d6b70d,0x60855d6e15c10822f4,0x2008005f000008081,0xf008a05756e17410a9,0xadc29821035b803042,0x42bd042025747e1750,0xa98fc29a01031f803,0x40246bd046020003e0,0x140b5af435809575e,0x857012a8bd0a80240d,0x7a00c040687c06a810,0x5e80001000a700018])
def xX : List (List Nat) := qE
def yV : Nat → Packing
  | 10 => sY
  | 9 => d7
  | 8 => d6
  | 7 => d5
  | 6 => d4
  | 5 => d3
  | _ => emptyPacking
def xY : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 177 223 4 13 7 2 sX
  | 9 => lookupWord 185 697 7 15 9 2 d2
  | 8 => lookupWord 39 199 6 14 8 2 d1
  | 7 => lookupWord 11 35 3 11 5 2 d0
  | 6 => lookupWord 1 3 1 7 1 2 kZ
  | _ => fun _ => none
def zB : Forest := ⟨1215,10,fun j => vD[j]?.getD (0,0),vC,xX,yV,xY⟩
set_option maxHeartbeats 0 in
theorem zK : graphValid zB (boundsBefore z3) = true := checkedGeometry 4 0
def z6 (j : Nat) : Nat := (readWords [0x764260437506145074,0x436550744365407443,0x653074436254734362,0x657236165272361651,0x723616317236163071,0x362652713626427136,0x264170435540704355,0x307042554070415550,0x704155407003547070,0x35450672465416714,0x653065360765653607,0x546536074360634121,0x606341106060416160,0x604121605341216050,0x412160134121566307,0x635663075453641483,0x531322715313227053,0x132261531022715310,0x225051643070516430,0x505135227147145542,0x463462604606417142,0x560343425603324256,0x32142530343425303,0x324246037342460371,0x424603434246033242,0x430376374316743743,0x167337431663374316,0x623743164337401475,0x374014633734657337,0x346572363562323635,0x622136356210363462,0x323634622135461480,0x354614403546143035,0x461420313522823135,0x225231352232313522,0x213134223231342221,0x313122723131223231,0x312221310522323101,0x223231012221304656,0x652434038317632675,0x154630701546306015,0x463050154630101545,0x307015453010154230,0x101541307015063460,0x150630601506301014,0x463010135322521313,0x228213132275072455,0x740724555207145574,0x71455640606418106,0x64161060541810605,0x417103645676036456,0x650364566403645483])
def z1 (j : Nat) : Nat := (readWords [0x6453043210043201,0x64500432100432010,0x641306357005416106,0x410043210043201064,0x25174200502100640,0x251742004610006402,0x517420040210064025,0x174200401700640251,0x732003610006401517,0x420050210064015174,0x200301500640103457,0x203042106324067501,0x54021063200675010,0x540210630120364103,0x201006042537420030,0x270052345207130072,0x600523452071300523,0x5234520713004270,0x52344207130052400,0x523052071300623005,0x230520713005230052,0x305207130042600523,0x52071300412005046,0x10432010421040351,0x306420124300403113,0x64201632004031130,0x642012430040311306,0x420123500315406417,0x200162003120021053,0x21061031200210530,0x210310312002105301,0x602103120021043021,0x31030420315240103,0x600304203152401034,0x3041031524010340,0x30410315240102300,0x254064170302604002,0x460057610056201024,0x600576100341010241,0x4321004320102036,0x1674012501020340,0x16740126010203400,0x167400146101450057,0x630012561014500576,0x200451010145005761,0x5620101450057610,0x45201014500576100,0x342010145005761003,0x415101450057610012,0x31014064135200402,0x100140641352003021,0x1402413520040210,0x14024135200302100,0x140241352003017001,0x324023401034021013,0x200234010630210132,0x2340103402101304,0x607241072010013046,0x72410620100062435,0x247003640000624352,0x470034500006243524,0x700273000062007561,0x5620200620075610,0x34102005123542700,0x435000051235427003,0x240000461735642056,0x434004517156020561,0x200045171460207412,0x412314602037120,0x3247065140651000,0x32470641202506000,0x264362471037520002,0x643624710365200026,0x436247103462000214,0x726531065320002147,0x264310473200014236,0x427104362000142364,0x271043520001423642,0x710325600014236427,0x103251000134746530,0x65400001257465300,0x654000012474653006,0x540000124746530054,0x360001247465300543,5144848246007107,0x400124736542054324])
def zE : Nat := 0x5021042110c0300c03
def zD : Nat := 0x24914891a0c85405
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rO : CutRow zB 5 0 2 :=
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x7570) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rP : CutRow zB 6 0 19 :=
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [111,0x311660000238033954,0x395f3a36481e4dbfb1])) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rQ : CutRow zB 7 0 137 :=
  (@joinRow zB 7 0 64 73 (@joinRow zB 7 0 32 32
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [65589113922,0x354b2f19185c5c3400,0x4fc7ad00d8a4cf9f00,0xa4be00d000a7a99000])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [450974194500,0x6259441f4e1a250b18,0x6118056a663a071871,0x5c536b661845495029])) rfl (by decide +kernel))) (@joinRow zB 7 64 32 41
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [391999664211,0x182327273c181317,0x12683b18185d111845,0x1800442b005c472337])) rfl (by decide +kernel)) (@joinRow zB 7 96 32 9
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [94560845863,0x44006c5a5d511a,0x583269584a182f1a18,0xd1418491866454010])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x1818403d3232183c18) rfl (by decide +kernel)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rR : CutRow zB 8 0 387 :=
  (@joinRow zB 8 0 192 195 (@joinRow zB 8 0 96 96 (@joinRow zB 8 0 32 64
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [631370139013,0xd69c0000848a00a400,0x8f0000b6a887008200,0x88b6808a0000000000])) rfl (by decide +kernel)) (@joinRow zB 8 32 32 32
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [759447997399,0xa2000000b5b2a3bd00,0x8a84ca8981c4848e00,0x829d00aa84c3bac898])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [917877271204,0xc00000b583a884d3c6,0xbc84bbd984ac009fb4,0xcc9e84cd92b8c100])) rfl (by decide +kernel)))) (@joinRow zB 8 96 32 64
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [569161389987,0xa5d48484c3ce9ac580,0x84a18497c5d1bfa4aa,0xa6a88080b6b9b6d1])) rfl (by decide +kernel)) (@joinRow zB 8 128 32 32
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [194720982107,0x582828462842005b,0x188684a4d6a4b9848b,0x8a8484a3bf009600ae])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [103486457406,0x584658182856451815,0x5d28555b2863180a18,0x185d00585b563e582a])) rfl (by decide +kernel))))) (@joinRow zB 8 192 96 99 (@joinRow zB 8 192 32 64
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [172474397509,0x4626235b5d465a,0x5b27671815186e1818,0x5823092a2d5e181828])) rfl (by decide +kernel)) (@joinRow zB 8 224 32 32
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [95968303128,0x1846464667581c5818,0x462346241826185e18,0x585b2c586d334c0046])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [378248118824,0x4618285b1821180818,0x1828465b5b410e7320,0x45082358005d15183e])) rfl (by decide +kernel)))) (@joinRow zB 8 288 64 35 (@joinRow zB 8 288 32 32
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [190761497112,0x3f581822416e585801,0x235b083e1828434618,0x18232c0856575b1d6d])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [302208009512,0x52112d0c4558461858,0x232c56234658330818,0x285b182a5b1846185b])) rfl (by decide +kernel))) (@joinRow zB 8 352 32 3
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [198328862243,0x5b43283f18185e6546,0x286a01574546000027,0x181818282d5d004618])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x181827) rfl (by decide +kernel))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rS : CutRow zB 9 0 122 :=
  (@joinRow zB 9 0 64 58 (@joinRow zB 9 0 32 32
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x0) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [569431268740,0xd6b6b6bba48c8dbfb3,0x81d600000000000000,0])) rfl (by decide +kernel))) (@joinRow zB 9 64 32 26
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [706987853014,0x81a4d600d6d6000091,0x8184bdc5008484b4d6,0x97daa4ab9d8400c984])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=(readWords [0x8cbf8495d68a94,0xb7d6d6c9af94bfa4a4,0x81848481a499ccb48c])) rfl (by decide +kernel))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem s9 : CutRow zB 10 0 10 :=
  (panelDispatchBlock (pos:=zE) (neg:=zD) (kw:=z6) (panels:=z1) (data:=0x0) rfl (by decide +kernel))
theorem zA : mixedTables zB 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty zB 0 0
  · exact mixedEmpty zB 1 0
  · exact mixedEmpty zB 2 0
  · exact mixedEmpty zB 3 0
  · exact mixedEmpty zB 4 0
  · exact rO
  · exact rP
  · exact rQ
  · exact rR
  · exact rS
  · exact s9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q6 : Impossible false (graphGoal 1215) 10 (vars 1215).toFinset := plainA (q:=191) (prior:=boundsBefore z3) (before_sound z3 z4) (by decide +kernel)
def jU := extendPerm z3 11 [(6847,0),(1887,3),(14175,55),(8059,11),(17275,29),(17390,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xP : Known false jU := extend_ok (m:=6847) z4
    (lowerFromFull (q:=1215) [2, 1, 2, 4, 1, 1, 4] q6
      (mixedIndex (g:=zB) (i:=0) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def qN := extendPerm jU 11 [(14143,2)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yB : Known false qN := extend_ok (m:=18111) xP
    (lowerFromFull (q:=1215) [2, 1, 2, 4, 1, 1, 4] q6
      (mixedIndex (g:=zB) (i:=1) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def qL := extendPerm qN 11 [(17087,0),(9535,17),(4959,3),(2415,13)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem y9 : Known false qL := extend_ok (m:=17087) yB
    (lowerFromFull (q:=1215) [2, 1, 2, 4, 1, 1, 4] q6
      (mixedIndex (g:=zB) (i:=2) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def jN := extendPerm qL 11 [(2239,0),(4927,85),(6975,17),(2399,3),(9567,55),(4975,13),(7023,86),(2427,29),(9595,11),(9703,158),(12782,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xI : Known false jN := extend_ok (m:=2239) y9
    (lowerFromFull (q:=1215) [2, 1, 2, 4, 1, 1, 4] q6
      (mixedIndex (g:=zB) (i:=3) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def jR := extendPerm jN 11 [(2751,0),(1343,2),(18751,26),(1375,15),(18783,56),(1391,57),(18799,58),(1403,7),(18811,87),(28135,54),(6638,31),(28142,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xM : Known false jR := extend_ok (m:=2751) xI
    (lowerFromFull (q:=1215) [2, 1, 2, 4, 8, 1, 4] q6
      (mixedIndex (g:=zB) (i:=4) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def jJ := extendPerm jR 11 [(1727,0),(2367,2),(7007,15),(9583,57),(4987,7),(17341,23),(14318,31)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xE : Known false jJ := extend_ok (m:=1727) xM
    (lowerFromFull (q:=1215) [2, 1, 2, 4, 1, 1, 4] q6
      (mixedIndex (g:=zB) (i:=5) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def qP := extendPerm jJ 11 [(42687,0),(44351,2),(47967,15),(53087,3),(44923,7),(69499,11),(60349,23),(69565,59),(42983,6),(45031,88),(53230,31),(60398,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yD : Known false qP := extend_ok (m:=42687) xE
    (lowerFromFull (q:=1215) [2, 1, 2, 4, 1, 1, 4] q6
      (mixedIndex (g:=zB) (i:=6) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def j2 := extendPerm qP 11 [(58559,0),(64191,14),(51007,17),(54079,2),(46431,3),(43887,13),(54127,58),(48507,11),(43951,78),(43453,23),(64445,59),(49646,45)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yQ : Known false j2 := extend_ok (m:=58559) yD
    (lowerFromFull (q:=1215) [2, 1, 2, 36, 1, 9, 4] q6
      (mixedIndex (g:=zB) (i:=7) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def j0 := extendPerm j2 11 [(58047,0),(47935,17),(69439,26),(44383,3),(74079,56),(50043,11),(58235,29),(69102,30)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yO : Known false j0 := extend_ok (m:=58047) yQ
    (lowerFromFull (q:=1215) [2, 1, 2, 16, 8, 1, 4] q6
      (mixedIndex (g:=zB) (i:=8) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def zQ := extendPerm j0 11 [(44223,0),(44735,53),(52927,14),(54975,8),(42815,2),(44863,85),(53055,17),(60223,26),(42847,15),(50015,55),(58207,3),(60255,56),(42863,57),(47983,86),(60271,58),(69487,13),(42875,7),(44411,29),(60283,87),(74107,11),(44989,59),(69095,88),(69607,54),(48110,31),(55278,30),(69614,40)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z5 : Known false zQ := extend_ok (m:=44223) yO
    (lowerFromFull (q:=1215) [16, 1, 2, 4, 1, 1, 4] q6
      (mixedIndex (g:=zB) (i:=9) rfl rfl (before_sound z3 z4) zK zA (by decide +kernel))) (by decide +kernel)
def r7 (i : Nat) : Nat := (readWords [313487,0x1a284060808057fc10])
def rB : Packing := (1,1,6,0,0,0,0,r7)
def r9 (i : Nat) : Nat := (readWords [137887971,0xc4814a28004c828,0xa8000000128807217,0x108490827828b80af])
def sZ (i : Nat) : Nat := (readWords [76841487043713,0x8140206a2410640600,0x40e1d00022e2050212,0x800011103640685c1c,0x10c04820d80802c260,0xc58342c08544800504,0xd78c021e1c04000874,0x80d0b4609048382010,0x50c640685848241c1,0x80283c30342c2718,0xa0c10040161a18161,0x413918d06080200bbe,0xabda425b7f9a15910f,0x2e85d003ff5cc10ffd,0x30043ff55010ffd420,0x42ff60810bfd83042f,0xf61010afd86042fb60,0x810bbd84042f760c10])
def rA : Packing := (11,2,6,0,0,10,0,sZ)
def r8 (i : Nat) : Nat := (readWords [9042383627059296,0x6397c47943e4890180,0x297152608243b403c,0x8700800082947f1180,0x1c3285b90ec419200,0x2c8c93c003182c,0x4b157140c721300030,0x50003410000003d1e5,0x37c6746e01704d4450,0x5c06907602c0011095,0x282796c1628578340,0x1c1c40e9129862001,0x8200000514a043340,0x4082000000144000])
def dB (j : Nat) : Nat := (readWords [0x5e531855aca28df,0x80d3485b10aff144a3,0x3b08ac2279015e405,0x3fc243f74904e6f88,0xcfe84131fd4095e405,0xa6492532492f60487f,0x42099e4055ba01ef50,0x25bee9209cfec0916e,0x8073ee9209c7a80887,0x9e449669080ff091d4,0x57d0116e807bd8120,0x8116988c51b8c1680a,0x3e0241874390b410,0x783414020482f09088,0x6c0001070642100bd2,0xd8b0ab2a8e8a9f66f9,0x864f8f625819f3761b,0xf6b59860d6e54d414a,0xd153dcdf324ab24877,0x19c4f0f42b054002c9,0x2cc12c983ca94cb84c,0xc11eb80cca3ca134aa,0x60cad8a94ab9b89846,0xb856a15aaa38cbc0cb,0xc4a168b846cad4986a,0xa134b9e6c95a9836b9,0xd0c958b9c8a146a956,0xaa58aa46985aca3ffd,0xbff7def7ddfafeffcf,0xf618106101060c1060,0x8105cc10550104c010])
def dE : Packing := (36,3,6,524295,51,10,1055,dB)
def dC (i : Nat) : Nat := (readWords [0x4200118060050,0x390014553e041769a0])
def dA (i : Nat) : Nat := (readWords [439822067446272,0x81c306401038600041,0x8002029b9673502d1e,0x1900abf6897361810a,0xfb6a57360810ebe5c1,0x3061810efa5c130608,0x10eee5c13061010cfb,0x649825cc10aef68973,0x610108f72a54260c10])
def dD : Packing := (8,4,6,0,0,8,0,dA)
def vJ : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xffffffffffa8c12191]),0x7c002100),(0x100d1cae,0x38d1cac),((readWords [255,0xffffffffffffffffff,0xffffffffffc4146207]),(readWords [255,0xffffffffffffffffff,0xffffffffffec000203])),(0x5308cf8,0x139088f0),((readWords [255,0xffffffffffffffffff,0xffffffffffa160574f]),(readWords [255,0xffffffffffffffffff,0xffffffffff806f560f])),(0xa82987e,0x390807e),(0x1008e070,0x7c72e050),(0x4202ff80,0x106f7d80),(0x0,0x0)]
def vI : List ColumnInfo := readRows 40 (fun x => (readField x 0 16, ([64,0,32,16,8,128] : List Nat).getD (readField x 16 3) 0, readField x 19 16, ([0,36] : List Nat).getD (readField x 35 1) 0, readField x 36 4)) 33 (readWords [7865053,0x76b5f1d6414005,0x1c0054400529005a40,0xf200c1400589004e,0x7675f1ce418747f1e8,0x186b5e8d602400271,0xb1700799000c8002,0xf900a040031c009480,0x25b904484006330029,0x4000e800a240053300,0x4987d5e8fa02400272,0x918725e8e4028715,0xe8e2028675e8ce0281,0x65e82c028545e8a802,0xb7d5f9fa40b725f9e4,0x40b6b5f9d640b675f9,0xce4070077100118022,0xf904a0802739041870,0x6f100218005e80002])
def t1 : List (List Nat) := qE
def yX : Nat → Packing
  | 11 => rB
  | 10 => rA
  | 9 => dE
  | 8 => dD
  | _ => emptyPacking
def t2 : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 5 23 3 10 4 2 r9
  | 10 => lookupWord 27 69 6 12 6 2 r8
  | 9 => lookupWord 2 13 4 9 3 2 dC
  | _ => fun _ => none
def q5 : Forest := ⟨1279,11,fun j => vJ[j]?.getD (0,0),vI,t1,yX,t2⟩
set_option maxHeartbeats 0 in
theorem tO : graphValid q5 (boundsBefore zQ) = true := checkedGeometry 3 0
def j8 (j : Nat) : Nat := (readWords [0x847465507548287565,0x753010647580103578,0x44026643171266431,0x212664311026523060])
def zZ (j : Nat) : Nat := (readWords [0x760215268407,0x140007602152684021,0x500076021526800214,0x756214263002130,0x7502157680021400,0x75021526800214000,0x724013674201273007,0x12142630021400070,0x121426300213000641,0x207854107502106412,0x78541065021064120,0x785410640710641207,0x854106402106412078,0x501064021041620746,0x810017200405707468,0x100162002305817562,0x75120023058175620,0x651200230581756206,0x417002305817562064,0x120007214135200402,0x100041202345103702,0x100412023401073021])
def vH : Nat := (readWords [160,0x4210842110c0300c03])
def vG : Nat := (readWords [208,0x64a49147434114642a])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rT : CutRow q5 8 0 8 :=
  (panelDispatchBlock (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=0x304020102040392) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rU : CutRow q5 9 0 36 :=
  (@joinRow q5 9 0 32 4
  (panelDispatchBlock (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=(readWords [25769937161,0x8096919089008e,0x8f8c9300858b828984,0x94888e8a810087838b])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=0x3050807) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sA : CutRow q5 10 0 11 :=
  (panelDispatchBlock (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=(readWords [38278,0x8d00000000000000])) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sB : CutRow q5 11 0 1 :=
  (panelDispatchBlock (pos:=vH) (neg:=vG) (kw:=j8) (panels:=zZ) (data:=0x0) rfl (by decide +kernel))
theorem y7 : mixedTables q5 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty q5 0 0
  · exact mixedEmpty q5 1 0
  · exact mixedEmpty q5 2 0
  · exact mixedEmpty q5 3 0
  · exact mixedEmpty q5 4 0
  · exact mixedEmpty q5 5 0
  · exact mixedEmpty q5 6 0
  · exact mixedEmpty q5 7 0
  · exact rT
  · exact rU
  · exact sA
  · exact sB
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q7 : Impossible false (graphGoal 1279) 11 (vars 1279).toFinset := plainA (q:=255) (prior:=boundsBefore zQ) (before_sound zQ z5) (by decide +kernel)
def jO := extendPerm zQ 12 [(27127,27)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xJ : Known false jO := extend_ok (m:=2303) z5
    (lowerFromFull (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] q7
      (cutFromKnown z5 (2112,0,2239,0,11))) (by decide +kernel)
def qM := extendPerm jO 12 [(17151,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yA : Known false qM := extend_ok (m:=17151) xJ
    (lowerFromFull (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] q7
      (cutFromKnown z5 (16960,0,17087,0,11))) (by decide +kernel)
def jS := extendPerm qM 12 [(18911,22),(28151,27)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xN : Known false jS := extend_ok (m:=2815) yA
    (lowerFromFull (q:=1279) [2, 1, 2, 4, 8, 1, 2, 4] q7
      (cutFromKnown z5 (2624,0,2751,0,11))) (by decide +kernel)
def jV := extendPerm jS 12 [(17403,89)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xQ : Known false jV := extend_ok (m:=6911) xN
    (lowerFromFull (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] q7
      (cutFromKnown z5 (6720,0,6847,0,11))) (by decide +kernel)
def jK := extendPerm jV 12 [(17405,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xF : Known false jK := extend_ok (m:=1791) xQ
    (lowerFromFull (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] q7
      (cutFromKnown z5 (1600,0,1727,0,11))) (by decide +kernel)
def jE := extendPerm jK 12 [(3579,79),(18941,4),(11774,159),(18942,160)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem x9 : Known false jE := extend_ok (m:=1279) xF
    (lowerFromFull (q:=1279) [16, 4, 2, 4, 1, 1, 2, 4] q7
      (mixedIndex (g:=q5) (i:=0) rfl rfl (before_sound zQ z5) tO y7 (by decide +kernel))) (by decide +kernel)
def j3 := extendPerm jE 12 [(58623,0),(46559,24),(43517,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yR : Known false j3 := extend_ok (m:=58623) x9
    (lowerFromFull (q:=1279) [2, 1, 2, 36, 1, 9, 2, 4] q7
      (cutFromKnown z5 (58432,0,58559,0,11))) (by decide +kernel)
def j1 := extendPerm j3 12 [(68863,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yP : Known false j1 := extend_ok (m:=58111) yR
    (lowerFromFull (q:=1279) [2, 1, 2, 16, 8, 1, 2, 4] q7
      (cutFromKnown z5 (57920,0,58047,0,11))) (by decide +kernel)
def qU := extendPerm j1 12 [(44799,53),(42975,161),(58335,24),(60383,22),(48119,46),(69623,27),(45053,90),(58365,4)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yI : Known false qU := extend_ok (m:=44287) yP
    (lowerFromFull (q:=1279) [16, 1, 2, 4, 1, 1, 2, 4] q7
      (cutFromKnown z5 (44096,0,44223,0,11))) (by decide +kernel)
def z7 := extendPerm qU 12 [(42751,0),(47871,14),(42999,46),(60413,4),(69629,90)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem zG : Known false z7 := extend_ok (m:=42751) yI
    (lowerFromFull (q:=1279) [2, 1, 2, 4, 1, 1, 2, 4] q7
      (cutFromKnown z5 (42560,0,42687,0,11))) (by decide +kernel)
def rE (i : Nat) : Nat := (readWords [0x5a2c1286c92b8,0x843c484150a4502713,0xc12251208c442103,0x34401f0f074381b0d0,0x6430170b05402080a0,0x4c24110803c1c0d065,0xc160a048200e063014,0x80301004006f6f129,0x4761d803fe887fd30f,0xfa81ff54bfe087fc30])
def rK : Packing := (6,1,8,0,0,9,0,rE)
def rH (i : Nat) : Nat := (readWords [1335552,0x4baed31538440,0xc1ffdeb0f6183e0600,0xa8c0b07e49b14e320,0x2839810909504c00,0x50a76d4868c100006,0x8bfa4c000000000083,0x709a00000028a80019,0xdc14911063a64efd1,2062370134,0xed2b90b0000000c28,0x9281131c40021b7200,34283569,0x241808c49c03280750,0x2389b83e000b92e08c,0x9128422147ccdc2,0x4b299c6cd4889ec33b,0x15a259e00915b38a81,0x356660ac43d82820ca,0x83712145fe1b30b939,0xf002000f12fa0743b0,0x39c1d0b445d640f03,0x5b1000194c00000010,0x45e02d07502ddb960a,0x713a47c0008c3e89f8,0x1470c2045041347100,0x1400820430050b11c3,0x5410032cc082000283])
def rD (j : Nat) : Nat := (readWords [0x6ffff64904012,0xa7fcc020224b7f64e1,0x30f024d2bfafe40a03,0x2481e0294604de32d2,0x2ffc68564541281bff,0x144081a63d8b81940,0x9fff785350254fffe0,0x2f017139c880000015,0x47ebf703c5804a327e,0x1f3e4c0082f1cf1be8,0x9c1b0004ec70629097,0x78125ffe0ca5ec0085,0xe09fb70ef058a20000,0xdc5fff81aae0670005,0xffd7000400fcfea200,0x2aaffec8001025157a,0xa85702d1ae1e9c8400,0x3ff3fc7f89904,0x14d7fe7f00184005c1,0x5620000af597d0ca8a,0x688f6fe300022685f5,0x54114bff14d63033df,0xf85f00ccb9c800caef,0x24afe865044340378,0x275f91338fb400f3f4,0x4a0073c6fbb087000,0x4c004ff0178007139c,0x9224a93c6a8dbca094,0xdffea8819f3f0e00,0x85a338ff5f0360058d,0x98227afe40ec8c0000,0x4fe7ff61784cbbc090,8725724279312382,0x14e3f504e40cc18553,0x8033003cfc0464a868,0x19c66172268a04d84e,0x148820c84045511124,0x69184211b10d424450,0xf4fc3981c641855454,0xd52428511404f1394b,0xa82900c2809c09094,0x1f0c00486a170520e0,0x86017c5e16e064904,0x64743a41c6518c6289,0xd565552c42c2487612,0x872188442d0320f834,0xb1303c1762a169585,0x5d3d4084844d304b51,0xc082018260882e2d96,0x540436024cd324c514,0x88e038120a0bd2b11e,0x2c86d204404a88a210,0xda2550438caf100d43,0xb0f8371270f0b83489,7888547798290776,0xe38c58a386e83a81a7,0xe378274c7106d06b16,0x9b6616155e45835535,0x255044aa44941c3e83,0xca39b3563403132e32,0xb02a526c2151e51b61,0x8713f11d0dc0c60720,0x4902300090414ae2e5,0x7352b8391cd48e6253,0x32c3c90c14ae12560,0x729829619cae324835,0x2c189609ca63257032,0x9859605cae2647132a,0x8b9589cb06a48172c0,0x994c04a40d98306c1a,0x32059b060c8126c3c3,0x6199b0251862641a84,0x81c2e0d5418ec10748,0x2830c498202c18ffff,0xefeff7fbfbfbfefbbd,0xebf549404c1100c010])
def rJ : Packing := (48,2,8,655366,67,12,1166,rD)
def rG (i : Nat) : Nat := (if i<1 then (readWords [0x46d2ef6d0e6207,0xb000048f9000000005,0x4c6c4bb48ca6097d01,0xf00000000000000000,197,0xec8a4109c785902e50,0xe5a00a0101c8f8501,0x720d3781340b4e400a,0xec00008421a0f450b,0x500000000000000fe0,0xe073000050bcc29,0x8100850520000700e0,0x20f098d17828141,0x90000208e000062400,0xd60b0000b032189,0x8c03bd8fe000072fc2,0x33a028302eb0e1687,0x968e540e720fca88a0,0x6d5d26d8087ea25b00,0x7a092e05b200900000,0xd5000008cb789a508,0xad0a1146feefc00788,0x2b700cd901988f070b,0x8b0b9e0e320cb00d9e,0x2a02cd80f50000903,0x9d00b0000000000003,0x18c0eac65e48cd886,0x55081d242041520ed9,0x82788a5fc223a4bc70,0x2a3026cd5d06d3084b,0xa4205624eb3ec6220,0xb200110e47053b0d4d,0xef8e90501120aec07,0x56088e429327e20294,0x67fa66306cc042f0f,0x26098e03754c58ced6,0x68122500437409000,0x90bed0c8609500a97,0x1428e870bf207fa08,0xb00007072c0c790c36,0x6a22c5a2e2d825a09,0xd0e8da83f0699884f,0x7a0000a0890000e04,0x7000000000000904d0,252124677,0x700000000361a00004,0x8375015302d3020102,0x5d010f410b8d800624,0xfab0ac00000000310,0x20000b03e000014ca2,0x80300008079a8bec06,0x5d016e013104a00008,0x4180000dec50000385,0xa000020abc8c670505,0xe0d87c282e5658a03,0x8d0a030dbe866b816e,0xc277c0eb026303500e,0x92005bed2d02356216,0x76e0042d00b08f922,0x26427686228b3e03a7,0x307609e226a02f80d,0x40aaca6c00baeac50,0x64d065c528fe25c205,0xde0b00000e0120849a,0x27e09a204ba836c05,0x89830486896dbb0550,7190580559873,0xd0000602c000000000,252434785,0x8b04e5021b083208d1,0x700000f6960000000,0x60cf0000206e00000,0xf0c4589e969,0x2e0b6f05aa0c0c8b1c,0x886d2d792212a9b041,0x5c004021000008902a,0x400000000c20c000a,0x1b00000c013000180,0xc40000c3300280,0x420000000001c0140,0x5000000000040000,0x8000000b00130e180,0x6006082001502,0x1c0080200000281004,17179942912,0xc1000000000000,0xc0307000001000000,0x2400000002800800c7,0x681000044052040,0x1810000000020001c0,0x30000800020c0001,0x83004042000180000,0x2040c1001080080044,0x802800000c1001,0x490c9000000040000,0x40001000000000000,0xb00000000d000007,0x108410000000d140,281612415684672,0xc00030000c0080000,853224244420736,2147483649,0xcd000000000001,0xc002000008080,0x3040000000000001,8796093038594,0x7100001002000000,0x3140000084000000,24576,0x200080000000000,290279659667456,0x40002000000000,0x1c0000000003041000,0x10000c0000000000]) else (readWords [798016,0xe85f900d000010d,0x80000a0d684eec100e,0x44c70cef0de2002102,0x2603fd439000000008,0x9908f200000000000,15050279416,0x2992cda18eb909bb49,0xb00a764c760c6304f0,0xc29400000000d47,0xa00008875220e56228,0x2ba8a0ec6c489f80b,0xb08350000f0a5a60fc,0x1a40df507d26e70a2,0x1b0c9e03d820c882df,0xf8000000000000000,0xe09e2091c2acc,0x60c6f87031929ca07,0x4f422e0630cd022391,0xe9be01ef05ffe6fe49,0xbc9280820a90e8900,0x40b84d760d7e041f8f,0x3383da210100fe252d,0xe2c9049a8316096d0f,0xb70f644fc28531502d,0xa98a6da24e7f8b4a0f,0x3540190cc407e5048b,0x5e50d242909034740,0x5206f0000000000000,0x80fd0000804c229,0xb70cabeeb80c5dcf8c,0x5c40dc1287b84b286,0x626600001894a8974,0x7c9c2168da2000000,0x10240000e0f1e8faa,0xf9d0ff0059fae5605,0x4b09314e2c0a3f0e24,0xafc08f12b00e0ddb0c,0x140a64061e09d00006,0xc886fd08508d6509,0x4d8c1e0ebd82140f7f,0x682e06b1040682ca86,0x9c0af64205876442c2,0x3c60662086b080382,0x90000d0b2cc83701b8,0x8c30ad00a2841e000,0x78330000000020442,0xb1c077f8d50000000,33858366672,0xe8f49006b892000,0xb8580000000000000,0x80ee401c2036000,0xa8f70000e885e,0x46285120c280b3b04,0x5205120da806400000,8112774649220,0x8000020b7f0a810031]))
def rC (j : Nat) : Nat := (if j<1 then (readWords [0x53d58f2b3c28eb,0x83a90e78393ce29376,0x8dc436c0d91359cd22,0x33fccd432b8c9b31e8,0xc563090c122ff0be22,0xe5cb622d3cb392c18a,0xda2a50a812994a3427,0xf09d626f4992261496,0x24dc8fa233c89b218,0xc82b20607d21e94775,0x1d3c7121bb86c21a94,0x67a198461f17d85bc1,0x62455014a050a13844,0xce128c480117842b0f,0xd83d40e4037d0d102f,0x70b4c29309a022507f,0x1d106b417a053c118,0x39c0da031c0b40284,0x66016404600cc0200,0x3400095304255c629,0x5717a5661894973e52,0x5d195317a566109531,0x3e55c9595714e56462,0x9597725641695724a5,0x61d695654e55c4f948,0x75a52618959072564d,0xf95718254c5595987e,0x554d394918a55c5c95,0x935255cd195515a55c,0x9495315e565d495987,0x256056953182558979,0x5985a5641f95716a56,0x62295656a55c0e9487,0x565641894874652610,0x949772558d394937da,0x61d9688739a5cd1699,0x70da26102d9034b662,0x2716559f4c5d698305,0xa4c602d98364589769,0x8724b65d12d974a45c,0xf69516e45c012d917,0x9a6055698744b26169,0x1604cb64cb68970cb6,0x41c91874e154d56897,0x2634c21716356164d4,0x90985da24e06887463,0x64e17d9775a6616698,0x14da261f2d977235c9,0x391206da649b699181,0xa65d169811a154da91,0x935da609490815da5c,0x112d976a4605791725,0xcb65cc7d7174b65939,0x1706da6608912060b6,0x55291315e45c1a6987,0x50b2614689744b65ce,0x68816da65c969875a4,0x5c132d926da21d9853,0x13db5c5e6898623249,0x92d9649a605a7d4179,0xa615369534a465d32d,0x9169a61da698159a26,0x2269916da481b68816,0x9a6622689871a61556,0x99381a4c112d987244,0x857697180b64606887,0x4a154d3698121a6047,0x69706e421d3698569a,0x24602d9189f64dd698,0x16da21da8d71864659,0x3698704b644f69826e,0x35c962d916cb64927d,0x4181a6095698559a24,0x5b69874e35c9a90814,0xe365e191514da66182,0xd9131a61c769985245,0x953716555a61c39181,0x4c465d111980042610,0x35870c4660421932d7,0x65c21098604660d259,0x784465c519954a04c5,0x71197384660f3d861c,0xf604a81534c464d23d,0x8618464e0159631960,0x53618120f644a59900,0xd665c3119548a640d8,0x9724ca640051877595,0xc1b5d8205625c32592,0x35760805d820c42614,0x119039764c23d8621d,0x54611d9411e4c5d498,0x50c465d28930854610,0x17553844649b119820,0xf244a59700d2614111,0x9180466223d8604964,0x8b019715061434d840,0x8c61c3059548165454,0x58508264d239860956,0x830d9217ffffeff7f,0xebfbff6fdffb7edfbf,0xeffbff7f6fddf7bdf7,0x9eefdd7b7f6ded7d7f,0xaef3fe77bff7fafddf,0x7bdf77edfcff9f73de,0x6fc7f4c1524815261d,0x405c5405c140505404,0xc54061930609306053,0x5c5305c1305893058,0x130545304813020530,0x60d105cd104c11020d,0x101cd100c110041106,0x1830604305c4305c03,0x4c030204301c43060,0xc10608104c0101cc10]) else (if j<2 then (readWords [726470055827474,0x5a4c0d94ff1102129f,0xfd080042d275fc88cc,0x7d08e32d5a4ca1d3e2,0x40ca037fc0042243d7,0x8c55d1318fe00895ff,0xf0e105d3009081b01d,0x1fd4e20010e7b410dc,0x82500e01ff0000d08c,0x5060b310c019f4978f,0xfef011359ed040b978,0xa3df8cc28180257304,0x85f341944407c3d214,0x551e90632fde35400c,0xe503bbfd64a14479eb,0xd08198bf837d44a804,0x4d40dfc218819dbe3f,0xb489689a11fd4cfa84,0x10a203b8c33a15081a,0x8f482827f7a6d123c1,0x44da94fef4220672f,0xf8fda88267aebe1881,0x981af92c4649019120,0x6189cd483f27d44849,0x174c4a3c749363910,0xd1e90630ef8780361f,0xf911abdb383b610b5f,0x13eba1b0203547ec9e,0x824206907fb855000c,0x14449c5d78852e1c8a,0xd47cc58b8f0853da08,0x8ff1343221a0f76445,0x2011fdd10858604791,0x431a4bbe9cd63940d2,0x2e1078c2057cbebd8a,0xa49a3359ed0427c0af,0x2080034400017c0bbe,0x142f9501b60af51a91,0xd3e015c308f48d5aaf,0x7fb0e401527fcb0c8f,0x4880466b0029f743c2,0x871a470e26782bd46a,0x479fea3fe0240932f2,0x82e30219bffe705d07,0x1346fc66140c0128a0,0x67b410f6821ed040ef,0xce05fa1e10d25033da,0x87b410f6821ed0428,0x1c0e41a23c2e3080f2,0x1c82d0944b4cc4ab92,0xce2024c969130ec472,0x814036174444546487,0xc211c18800fa1ed3c6,0x140189d9240742621c,0x3786b6b0562abd2aa,0x658220144644024448,0x13026719d05a6686b1,0x984442810b1861861d,0xc22c9108c470042084,0xa0a125175b8d0fa84,0x91844c10c39881a022,0x281e0f2a006d41e965,0x24896817824458500c,0xa4084731d22819a8e8,0x8710c1161542081887,0x40800f0dc18d0622c4,0x3623134400c041dc3a,0xb410e64af12e2d12b4,0xc795a0211a4c890171,0x84ac703384681383b0,0xe220c8188a0d08a49,0xd1a151cc378b28a70,0xf0bc1ea0a42d09180e,0x385108e88686e0fc0,0x813f0686165689024b,0x11a661a31087840148,0x19060ac461ff058434,0x7c17695a070700e436,0x4a0d216e0307c8499,0x649f2066215043f30f,0x6e0d2881070d40f81,0xd83606a0bc2683ac48,0x1c0004c00c0ba6cd9,0xa72682994e633984a5,0xe997565c3964256995,0xa523942e4f4936a4c,0x925246e917643e908,0xe4048f223ad8e4e378,0x8d5a32f8c462db8aca,0x27f895e23f88aa2048,0x74a1ba866e175854e1,0x3484520f9833a0b682,0xba09281f205780ae00,0xf7fc9fd57ecdf9e7e2,0x1f357c11ef47b11ea8,0x7959e2c7871dfa7741,0xda57601d607501d0e7,0x3d1ccf728dc83718dc,0x4870b9c0b6f8db9f6d,0xfdb596ccdb046b9dac,0x76aa1a8a69c1a32676,0x99c266959796529913,0x63e18c862598786119,0x81b5fd17d85eb57775,0xd2d7275c216be5a856,0x7e598962858455e256,0xa558f559d51e53ad4d,0x2529d49851f1456510,0x541650013d74ead37c,0x4d3d3384c4d2ee4b05,0x2a149c5249489120c4,0x7b91ce46bd18e45511,0x2744210ea430108b41,0x3901e402cfe43efcf8]) else (readWords [49292039,0xbc14abdfc307b7cc69,0xf38145081a23fe8819,0x1ef881084fe013a08,0x547682bc08c9d1ec34,0x420438ffa252847172,0xf00810a97f7d114b96,0x18fbd23190f884c4f4,0x813469ff92003369f8,0x4009499a625fde088b,0xd9571903cb803233ff,0xc88b00020444389183,0x5f70913be00324f1dc,0x2c8dded86c01980f50,0xa327ffc4d185021e1,0xeaea8810aefea20a20,0x21c3a7c2c01997181,0x10f88498f25040429b,0xfca5410010e5d2cc70,0xe2c3a137e3d9104747,0xe100211bfe003255f9,0x8051aff1044a87d892,0x18cffb7184019ca08c,0x87321269f5983a927e,0x8501b41251f09a0f6b,0x1888a174c4a3578cfd,0x210bcc0c3ed2197fff,0xc5a3080e0854206d53,0xf4482041535911d8fe,0x7e60441647c503243e,0x1da8c958204200811a,0x1fe7da913334029feb,0x118511ff95848330f7,0x3e7400488bfa10023c,0xf83f022cfaa8023037,0x9971f140d0bd62a22f,0xfcc0411b7fe140a092,0x34f15091b7a4be1159,0xfe903cc780896fed48,0xa13dfa9b0021400d7b,0xdd44fa02228de1002,0x133aacb806633f2003,0xa90193ffd31033c7db,0x499213760a107c5632,0x2af8e408a3437a247f,0xe881e00c000d411ff8,0x7d00ad07f708804df7,0xf90499f420643be040,0x300a502e0cffc28cfd,0xb7f8547a889a4efe01,0x2ede01555805373f06,0x1200010e3fa8822a3a,0x7aa090010e1ff85000,0x1986fd2c68238d7c22,0x2ebfff2a428517fc9b,0xa8410a1f71f44c0412,0x57e97c411b32a94329,0x7ffffd6190000804d7,0x5e700646fe1268cb5f,0xf104ccfcff92080004,0x45cd025064fff4c40c,0xe5fc1be9a60a06959f,0x41125d9df21a1483f1,0xfded08000440da5ff8,0x4202501a17fb00de7c,0x2061295c0253e9041,0x97a409b4cc798240ff,0xe02840cc6e4128bfc8,0x2002175fe9da0021ad,0xfcfcc2a1437bfa2401,0x219fec02de721f20a,0xb1e1050cc027924e7,0x86cfd42065dbea0a2,0x100a657b3a1c08577d,0xe82042d61ab1a8fe00,0x8b97fa808bb9e8091a,0x5dd54108077c7d86cc,0x24403fc56420a194f,0xc88518f58c28b9e184,0xa8033f3ff4214410a1,0xe9ff6e9016358512bd,0x7c54440093b110c3e3,0x680033698595029012,0xff94541840888b876c,0x6054c5fe564c819b9,0xf40090801ff67a5861,0x1f58220371f4120e0a,0xf50952483fd0610217,0xde28040850fffc0150,0xdba624048da7c412d9,0xa924df302a3bbec500])))
def rI : Packing := (259,3,8,2490403,102,14,1251,rC)
def rF (i : Nat) : Nat := (if i<1 then (readWords [0xa087405c06c402,0xf82ba83696c9af3800,0x20581025c55122e28,0x1908bb4a800000001,0x279141156dc2ea0bb,0xe97b882043dd877c92,0x7e075027bc12c0b200,0xc016c9d214d30d80,0x707200000000,0x814000000000000000,0xd18472f34d40000000,0x141af8c80100a06ee0,0x7884c906413302cbad,0x3f3a040001ae400004,0x2d0000804382d35bc,0x90b842700000000000,447209371760,0x980000000bb4342200,2732581424,0x820e832a09a03edc80,0xb16922440004012219,0x4e0c0000287fd0fc00,52340721250,0x46c696615920d28070,0x80e051ead519854,0xe2638088000000,0x413941e80006b6800,0x2444e038214461a9a,0x16103679540003456d,0x853a85c0003c8b402b,0x30923252c21f87c50c,0xc00030140000615e41,0xdb244ea87203400008,0x3a461b0000000361c8,25389635043328,0x713ba28f13bb09e000,0x16c989b88095c8fb40,0x600003132000000000,0x4c17112c62370304,0xc35b963604cc50a20c,0xf77192b6d10e82a50f,0x631740ab295000100,0x6d63651b4110921c40,0xf29800000000,74100774405169229,0x10a3d0b69457501415,0x540fb0317108901300,0xf1ca26ba6b88be0286,0x581671518f8301a3a0,0xf1eec2f0000,0x804902c4e42645e514,0x8000044038c3e0620e,0xec85cb8165902a0d5e,0x1c12bbd05e0184c438,0xcb87943ad3ec2048a8,0x28787ab3655c428194,0x1faef8ada8b3748400,0x2503606e46fd88010,0x4d7081c13778dcc264,0x8bd60afae8f62d08a9,0x85080001451718,0x9001e8024846210400,0x7c65112471b40,839,0xbc2107f6240000782c,0x299202d9807d850c16,0xac016aa2590a10aa00,0,2693547160,0x53210ebbae1437c852,0x78ed02f9847369f101,0x9400433e11227d0d60,0xa563100bab4d2307d4,0x428041e866819fd861,0x848f089b0acc252897,0xc044e037053e073a08,0xb90a64000079818df3,0xe02fa09fe0b0531d0,0x591863ad48015abd14,0x24360e4221b80e38a5,0xb0ca72a4841bc7520f,0x4801bc1df04718c741,0x2d064b8c8000142fc4,0x4550ab000000035183,0x83346af14c70608008,0xd96be4c4639a02e000,0x304080000000100181,0x20000001450c6153,0x201000280026102080,0xc000824d000203000,0xc00430c0202006,17321984,0x383000040001000000,0x810000000e040,0x4100010d0801800c2,0x40040000004143,0x1000000140000000,0x1009000002000000,0x10400020c0000000,755981361152,0x1000000000000040,17799418220544,4604204941377,0x6000100003087000,8796093022208,0x400c6080080000040,0x2040005082000080,0x1000200000000042,0x40040005080080080,0x1000000040000000,0x41000000040000001,0x80006000001000001,0,0x1000000000000000]) else (readWords [12087997691,0xa781186efec4a18424,0x90a80c8847a92012c1]))
def dJ (j : Nat) : Nat := (if j<1 then (readWords [0x5a2c6b4e344b82,0x353242352c282e4709,0xb5145eb04a292e47c9,0xb4afc2152e1f2e2a66,0xaa76942a4e8cb49462,0x2e2e0cb491c9950529,0x240a0c34b454330e5e,0xae4cc9b511e6aa4717,0xae4989b4ed1a346149,0xb4f20f341467a633e3,0x2a2c54130ed41512c2,0x34ebe2ae0e9632a5c9,0xb4748215244f344d8f,0x34cd8f152ddeae490e,0x342ca7a831e12e485e,0xae50cab46ad634460f,0x34e654130a02352b89,0xb517142604941317e1,0x2e300e344409b43754,0x32ea54b2e5cf150dd6,0x2ca9cf34a69a302c4f,0x34c68234c9dc30f354,0x130d669536692e474f,0x34268e344a89b4751b,0x2a2d1c30f30234e9d4,0x1517d41312c9b42fde,0xb4e0e5aa7709b4af57,0xb245cf150e423525e3,0xac079eae48dda63569,0x2e48272a27c13524c1,0x3449c1344e811503c1,0x35255ba63384b4d544,0xb4e341353110b46626,0x26160e942981352d01,0x3475d394318894318d,0x34665332e1c19526c1,0x34380db44686349516,0xa83293344086348304,0x9522d594060bb4a644,0xb4e390b2b112350290,0xb2a588344547b47097,0x2616d0aa69c8344f48,0x34021ca630982e01a1,0xae2e0834424bb4ad90,0xaa38252a271e241764,0xaa4701350989151155,0x2a69c5b4b04b34761b,0xa8320134c9d534661d,0x263145b4a259ae0159,0x2e238db4464a34ed81,0x352cc135314134e9cd,0x342705b4af90aca9da,0xae0105b4b0a0ae289e,0x2a48de2e48c9341541,0x15359032a0202e2e00,0x1522c0b4408fb0c292,0xb040642a4707340243,0x34a346b44243b48345,0x34a244344342b4e351,0x328011b0807ff3febf,0xdbfcffb7f7bf6ff6bf,0x5ff5bf4ff4befbe7fd,0xfbdf7df3defdebdd3b,0xfbbf7befbebbdfbdbb,0xd7bbfbb7b7fb7baffa,0xfbaf79ff9fb7ef7eb7,0xb777f77b75f5ff3ff3,0xf73ef3eb3bf3bb3af3,0x7f36f2beffaff2feef,0xeafdafbef7ef7af6ee,0xfedfabfebfabf6beeb,0xdebdabcebbeb7eb5ea,0xfeaeeabea7e8fe7fe7,0xfa3fe3ee2fd984c152,0x64530549714c152261,0x30548914c15265d205,0x49714815254d205495,0x148152645875013161,0xd4024d875009161d40,0x64d71500985c54024d,0x71501715c140505705,0x187505405c5415013,0x15054065d31501904c,0x5405c531500984c540,0x25d3150192619305c1,0x864c15161930481864,0xc09161930205864c17,0x26093021d824c08160,0x93021d814c1985c530,0x641714c0985c530589,0x704c1315c130485704,0xc0815c13061d624c18,0x558930605624c17258,0x930595624c15158930,0x261624c08758930615,0x604c18258130595604,0xc08758130609514c17,0x254530261514c19648,0x13061d204c18548130,0x605204c172481305c5,0x204c17048130595204,0xc16348130581204c15,0x348130545204c08748,0x130205204c19520530,0x5c8814c1532053021c,0x814c17360d105c1834,0x40985cd105c5304409,0x74c11065c834419161,0x830245860c09760430,0x619710c1941c43025d,0x83041976081064d820,0x41874c010619300418,0x54c01060930041981c,0xc1064073041821cc10]) else (readWords [3549275,0xf610c3eb16a0f78313,0x259a16018b360a9f10,0x20ef08ac84e1493586,0x87710ef811806dc08,0xf490f0c6a2601ae509,0x1c1046648f7d2431b8,0x43c342afe64645d213,0x4087bd144b9847522e,0xe8c4dc189c047018f3,0x90d40b2e8594b1081e,0xdd0b3e0241dec472b4,0x246af906806788830d,0x68cb760514584df01,0x20f2e850c1058f0f02,0x12ae845fa09e01cca1,0x5e22d910c023488b22,0xf7a20b6b88720e6891,0x61514304a0dbca8c60,0xe8e20d8076910fd811,0x7a90d807384217041,0x53cc4838e04c75c018,0xcfa233c22ea4d14722,0x9c443187434d85e01b,0xbdd050c0a029f98a72,0x13bd9053f810ce1120,0x1bc030704135d0af09,0xef113809617a19e11,0x20378896350dbae58d,0x7e021a7f9341653844,0x7e035025020fac5622,0xcfe9244cb3f121cd55,0xc7b8864c89013b01d,0x795318f350dd01ba03,0x7a03b66826fc047792,0xb7f311117f8218f42,0x1cb2d5070ea9419d91,0x57940032cf021d52c5,0xbc1436811322179850,0x6e80d0127f446265d6,0x8920dec0680a3e0631,0xc422051e818c991172,0xc18eb8031da118bc40,0x835e821bf00c4f086c,0xe0733429aa12fec110,0xfc119028f818f73426,0x200e30411f80c9b23,0x4047fc04859147c0c6,0x3a843c721a0e384719,0x239fc10ce05bef9220,0x3ffe3641203e90c66,0x50ff58992bf5c4c93f,0x1c110003813ff024e7,0xf081932f1432f4d18f,0x39aa643fe2240373ed,0x140dcfb45df7c91013,0xc18dcad880270dc441,0xc26b480c20266c4589,0x9250d2e0e8874ac26,0x92b88420217891a0d,0x54742281b6482c81d0,0x747281a198119450c3,0xdc381a4a5e26c27825,0x823e0d20001d023017,0x46741d4c4443144021,0x780780c17119a25e17,0x55c6c3c25749010c0d,0x501824c2079640e40f,0x813e19f0901b344081,0x825016c00350601813,0x40e81fc01801f8901f,0x81f01a81300bc0bbe2,0xfdd3d87d57ce7cabc7,0x7c23bb3b73b43af3aa,0x3a53a079e39a79538f,0xb8c788382f7e378b73,0xb6fb68b6476135ab55,0xf52b4df49345f4273d,0x33a335f3172e72a723,0x71ef1ab13f10f0d304,0xeff6fc2f52f0eebee4,0x2e02db2d76d36cfacb,0x2c8ac52c1abc2b6eb0,0xeab6a529ee98294e91,0x68b286282e7ea79672,0xa6ce67262a5ea59655,0xa50a4ba4824463ee3b,0x638e3423062ae25221,0x61e61aa1561160c208,0x6051ff5fb5f8df51f0,0x1ea1e45db9d7dd39d0,0x9cd9c8dc59bcdb75b2,0x1acda91a65a259c597,0x19358f98b98698197c,0x17516f56a563d5d559,0x55154c547d4293f53b,0x934d3112e52591f11a,0xd1811290e90bd06102,0x4fc0f64f24eb8e64e2,0xdccd8cd48d04ca0c5,0x4c28bd0b88b58b34ae,0x4aa0a58a2c9cc99493,0xc8e888083c7f87a076,0xc7046505c85504dc47,0x3b43402e82802181b,0x81400c806000023537,0x97ae57d433049fb027,0xd634c6141314d634e6,0x9b4cf68ae2729ae26,0xdeae4b142e3814130f,0x1eae4d18ae0ea22634,0x28952709b4efa92417,0x8c34b714152d49b4cf,0xdeae4949b4355b14ad]))
def dS : Packing := (203,4,8,5505121,119,12,1118,dJ)
def dN (i : Nat) : Nat := (readWords [592579168,0x10e441400000002b21,0xa46000182e001301e1,0xc617a1e0013ac00000,0x208000000001c3062,0xc000c03a1862803620,0xc233810023c068ec35,0x400191ca2600020efa,0x5404820000a1200000,0x224001208c05149e1])
def dI (i : Nat) : Nat := (readWords [6020,0x5e10350405c07c100,0x1805c203f01a840000,0x4004c083a83e24100,0xbc3d2400300b8604c0,0x35080fc02f1013005c,0x200233ae2400300b88,0x4d00300bc7d240260,0xb87e2401708002f01,0x70a33be2400300b880,0x6017080981adaa4a4,0xa73952358c21e86607,0x809e3745a561967521,0x434f905364ad238891,0xa83104800bcdb6c54a,0xa6902a5fd24c0a954d,0x2054bfa4a9a40b92a2,0x985779b72819520530,0xcebaa6d3930a8a61e7,0x95c971609514c2bbc5,0xcaa2b2a40986bb5a75,0x4984c540cfe152b8a,0xa290261f78545715c9,0x204c2f6cdb152a9a40,0x987dd1315c0985c530,0xafd172902e4a8a61ad,0x754da12613054bfa49,0x82a6b8a40a96adda64,0xc49361d40fec2e2982,0xa2902a58eb691a2660,0x730431b6cab4443902,0x985739b42819520530,0xaeb172a8aa690261ed,0x254d202613054a3bc5,0xcb4a40ae098636da56,0x89981cc108f736854a,0xa29026155e6dca0654,0x814c2bb4d9140ca902,0x986f49526855348130])
def dR : Packing := (28,5,8,0,0,10,0,dI)
def dM (i : Nat) : Nat := (readWords [0x2022120a00481835b,0xb4200000707b100030])
def dH (i : Nat) : Nat := (readWords [14600,0x5c1eb5c2b99303f50,0x54d515c57248130e5e,0x1722a571545204c379,0x2549b62a5534813097,0x39c42e551595204c35,0xd254cb948172545308,0x3b8c86d0a9545204c3,0x1c654db42a55148130])
def dQ : Packing := (7,6,8,0,0,6,0,dH)
def dL (i : Nat) : Nat := 0x78001b2d178400008
def dG (i : Nat) : Nat := (readWords [0x3507340795054d722,0xa571545204c22671b0,0xe2172a8aca90261474,0x8da54cb94817254530])
def dP : Packing := (3,7,8,0,0,5,0,dG)
def dK (i : Nat) : Nat := 0x1e0
def dF (i : Nat) : Nat := (readWords [56938811484,0x4da54cb94817254530])
def dO : Packing := (1,8,8,0,0,0,0,dF)
def vL : Array (Bits × Bits) := #[(0x840a108bec0006,0xd3584ac0e0a004),((readWords [255,0xffffffffffffffffff,0xffff24640550c50029]),(readWords [255,0xffffffffffffffffff,0xffff2c85b1021f1821])),((readWords [255,0xffffffffffffffffff,0xffff61200154008957]),0x503a0ef580c546),(0x4301e824009e18,0x874541086a3a18),((readWords [255,0xffffffffffffffffff,0xffff000b70212005e1]),(readWords [255,0xffffffffffffffffff,0xffff28a2b4371545e1])),((readWords [255,0xffffffffffffffffff,0xffff8880028a0a427f]),(readWords [255,0xffffffffffffffffff,0xffff04a7252e0a5a3b])),(0x105404001123be,0xd362442c60629e),(0x0,0x0),(0x1a908a001273c0,0x28189ad1958540)]
def vK : List ColumnInfo := readRows 41 (fun x => (readField x 0 17, ([0,1,16,2,8,256,32,4,64] : List Nat).getD (readField x 17 4) 0, readField x 21 17, 0, ([7,11,9,8,4,5] : List Nat).getD (readField x 38 3) 0)) 159 (readWords [274907791441,0x9834f401885000c600,0x11c6495e02410c0091,0x80017200074002c500,0x2620004e6043f002a0,0x400138005620014c00,0x259002320006600157,90731418249333168,0xd7818442186c60c21c,0xa003b000a20759c83a,0x9183ad381d462000f6,0x104a00670008c009,0xb18048718b57805842,0xc26e60120c6eb79075,0x3324bc81201a00518,0x80052974fe0bb002bb,0x6f05d08310af008084,0x24e40108cc025e000,0x50801617000d4000ec,0x489824f401085000,0x9cc01110017a000028,0x67a70338c600530000,0x6615a720ac468004e0,0x988560f82b580001,0xbc0022100294000356,0xab2f055284009c0001,0x1c925ec09008d5a7a0,0xac420cf3e06720857b,0x182b870005b4000250,0x73001060eb7a0750,0x2c0098b8012a000798,0x28214c3e0a7606493,0xd024213022f8014812,0xf5f817802a1efa10e0,0x24eb7d0750125abe82,0xd00806d3803462c4ad,0xc024116eb6e07508b2,0x4b7012045815cc0081,0x80027c000418012c00,0x29a563f82b400805b,0xc0002061e7e10e402e,0xb3f075201579f82b90,0x924fc0908044a7e02,0x44021b3f00d201099f,0x804901485f82400298,0x6fc0c2010013700024,0x20dbf0068060005d40,0xd1000c6801142257b,0x120225abb82d0212a,0x9fc1560098eee0c608,0x4097d004010040f802,0x5800958c04838642be,0x120200015d00011161,0xaf830880b1cfc18c80,0x5767e0ba402373f01b,0x200000f800580b3cfc,0x19c8094cfe0a7000a7,0x630530e4009c180116,0x5180007284afc024,0x14c77e06300a75bf0,0x3a805125f809002956,0xfa0aa023217b090021,0x75bd83a810b0dec184,0x8426f601204801622,0x6c00a60800c8a9d,0xec14c0854e7e0a6402,0x13f00020175b783a8,0x40925bc0902044ade0,0x241021b6f00d08109b,0x7804840a9dbc14c205,0x56de0aa102ad5f0561,0x156bd82b010ab4fc1,0x588057af60bc042437,0xb0210210fbd807810b,0xad7c1d44056abe0b42,0x2a75f05310124af81,0x20808dd7c06c4044ab,0xe0242021b5f00d1010,0x9af80488081d7c00c4,0x61ef610e042af7b05,0x702167af833880aed7,0xc17440402f60000420,0x15f00010169b783484,0xb4cfc1a480c02b600,0x242057b002021029f,0x801100815bc0082040,0xabe004200013900023,0xa70000c5005f800,0x2412f6008042096f,0x4081049f80210082,0x57c01040002c60001c])
def t4 : List (List Nat) := jB
def u0 : Nat → Packing
  | 12 => rK
  | 11 => rJ
  | 10 => rI
  | 9 => dS
  | 8 => dR
  | 7 => dQ
  | 6 => dP
  | 5 => dO
  | _ => emptyPacking
def t5 : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 35 135 6 13 6 3 rH
  | 11 => lookupWord 470 589 6 16 9 3 rG
  | 10 => lookupWord 338 423 6 15 8 3 rF
  | 9 => lookupWord 9 55 5 12 5 3 dN
  | 8 => lookupWord 3 13 3 10 3 3 dM
  | 7 => lookupWord 4 7 1 9 2 3 dL
  | 6 => lookupWord 1 3 1 8 1 3 dK
  | _ => fun _ => none
def zF : Forest := ⟨1407,12,fun j => vL[j]?.getD (0,0),vK,t4,u0,t5⟩
set_option maxHeartbeats 0 in
theorem zY : graphValid zF (boundsBefore z7) = true := checkedGeometry 4 1
def z8 (j : Nat) : Nat := (readWords [0x965808769465,0x755094657540946575,0x309461755092462752,0x855829948558298485,0x582975855829648558,0x295485582153824627,0x738246275382462752,0x823627738206276281,0x756661817566518175,0x664181756640817566,0x206567401065614010,0x656040106557417565,0x574153655141856537,0x501065374070653740,0x106530401056854187,0x568541655685314356,0x784170567640705675,0x419056754180567541,0x705675316056752150,0x560640805606407056,0x64060560640405603,0x408049568574495685,0x734847668442482343,0x424823324247233242,0x452343424523324176,0x809041768070318412,0x323154128526783191,0x267831212678311026,0x763191267631212675,0x412126184171261841,0x612618412126083191,0x260541812453237314,0x678090146780101461,0x801014608070146080,0x501460801013451272])
def z2 (j : Nat) : Nat := (readWords [533254,0x318240152300810252,0x493100532008015021,0x683021531076255694,0x810653000762326318,0x2751007620569180,0x38400076202691800,0x762000750208924604,0x653107361519420050,0x210070352810670142,0x300703228196702845,0x6783004321004311,0x67136584900463000,0x670365849004830006,0x350690857005460063,0x406918570054600634,0x69185700485006340,0x691857004350063200,0x786120761310632007,0x861206502106320078,0x612057021063200786,0x120541810632007861,0x205402106320078612,0x43021063200786020,0x850210632007860207,0x502106320078602065,0x191063200786020650,0x210630531470204312,0x6012648130040260,0x54077183620671200,0x540771836205217005,0x267091485008530042,0x654735820407300426,0x7658201073004260,0x76582010630042600,0x765820096200426007,0x658200862004260076,0x582007510041730756,0x930017300370208612,0x4017103407907562,0x37050031569275130,0x642300307214263002,0x140003016947530075,0x400030121426300214,0x301214263001830,0x2765068950056411,0x27600689500564010,0x276006895004530102,0x713352490039400027,0x133524900384000271,0x335249003450002710,0x352490034500025800,0x543290032410240691,0x856207512002406918,0x562065120024069185,0x620641800240671856,0x204716002106928531,0x75320021069285310,0x642800210692853105,0x726002106928531053,0x260020569485300754,0x205694853006840,0x2056948530064380,0x20569485300643000,0x205694853005320002,0x36012780029611020,0x360127800236110201,0x694853007540002016,0x948530068400020169,0x485300674000201694,0x853006540002016948,0x530064800020169485,0x300643000201694853,0x5730002016948530,0x53260016720598600,0x576010167205986004,0x650101620263180032,0x610015360168920045,0x110132681962007621,0x1326819620068210,0x13268196200651000,0x123683962005428000,0x765826713056230007,0x628269170451200067,0x283674206743000621,0x463581040610006214,0x635800305100054601,0x687200346100346006,0x875004571003284135,0x200402100032681962,0x7621000326817620,0x76210003268176200,0x659100032681762006,0x521000321413520040,0x210002674730820407,0x300025683764207643,0x256837642065320])
def zJ : Nat := (readWords [147776,0x8410842110c0300c03])
def zI : Nat := (readWords [276,0x89414e86824914642a])
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rV : CutRow zF 5 0 1 :=
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x43) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rW : CutRow zF 6 0 3 :=
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x2c1125) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rX : CutRow zF 7 0 7 :=
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x342d2111268edc) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rY : CutRow zF 8 0 28 :=
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [12,0x392711360349312e35,0x22002836140833a799,0xcededfcfa894bde2bc])) rfl (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rZ : CutRow zF 9 0 203 :=
  (@joinRow zF 9 0 96 107 (@joinRow zF 9 0 32 64
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [789196939174,0xb889a5b8cfa50098c8,0x918700000000000000,0])) rfl (by decide +kernel)) (@joinRow zF 9 32 32 32
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [892642041220,0xb89aa3c5b89ae1a2cc,0x9acf9e00e0aba6a4,0xdba5c6d89fd0009ed1])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [233070808122,0x409f9f9f9f9fd99283,0x9fb88a009f9fa3a3d4,0x8b009fb4b290a99bb0])) rfl (by decide +kernel)))) (@joinRow zF 9 96 64 43 (@joinRow zF 9 96 32 32
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [232837892112,0x36363624122438242f,0x15383b2b1f1332194c,0x3638301c3c0b383624])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [26713017613,0x45381230171d410238,0x36003c060f24201618,0x3e4b4718120b241c36])) rfl (by decide +kernel))) (@joinRow zF 9 160 32 11
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [22384416007,0x3a361e0b38361b1538,0x123606363b06092336,0x1204013606004c3829])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [14392,0x382a1238123800000a])) rfl (by decide +kernel)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sC : CutRow zF 10 0 259 :=
  (@joinRow zF 10 0 128 131 (@joinRow zF 10 0 64 64 (@joinRow zF 10 0 32 32
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel))) (@joinRow zF 10 64 32 32
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [715900584095,0xa60086c3b3c49fa68d,0xb6d6e500b09f9581c0,0xa08cc0000000000000])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [579342547159,0x86889fc3a681a686be,0xaa93868600b1869fcb,0xb000c9b5a6b19fbb86])) rfl (by decide +kernel)))) (@joinRow zF 10 128 64 67 (@joinRow zF 10 128 32 32
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [570333188757,0x86ca00b8b200cab000,0xd300ca82d39fb8a6b9,0xc3ca869f00dae485ae])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [869761451690,0x9f86009f9f86c0a19f,0xacadc7ca939f808fa6,0x8db0ddb6c1a6939f00])) rfl (by decide +kernel))) (@joinRow zF 10 192 32 35
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [233224222214,0x36360f12000f0f4d,0x4606ba9fb8b8b8879f,0xc29686979f00b09f00])) rfl (by decide +kernel)) (@joinRow zF 10 224 32 3
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=(readWords [252641295,0x4e4600364d423d3642,0x36004a060646063d,0xb4d0e0f4200000e4d])) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0xf0006) rfl (by decide +kernel))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sD : CutRow zF 11 0 48 :=
  (@joinRow zF 11 0 32 16
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel))
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sE : CutRow zF 12 0 6 :=
  (panelDispatchBlock (pos:=zJ) (neg:=zI) (kw:=z8) (panels:=z2) (data:=0x0) rfl (by decide +kernel))
theorem zS : mixedTables zF 12 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty zF 0 0
  · exact mixedEmpty zF 1 0
  · exact mixedEmpty zF 2 0
  · exact mixedEmpty zF 3 0
  · exact mixedEmpty zF 4 0
  · exact rV
  · exact rW
  · exact rX
  · exact rY
  · exact rZ
  · exact sC
  · exact sD
  · exact sE
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem jX : Impossible false (graphGoal 1407) 12 (vars 1407).toFinset := plainA (q:=383) (prior:=boundsBefore z7) (before_sound z7 zG) (by decide +kernel)
def jP := extendPerm z7 13 [(9599,91),(17343,60),(9711,92)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xK : Known false jP := extend_ok (m:=2431) zG
    (lowerFromFull (q:=1407) [2, 1, 2, 4, 1, 1, 2, 8] jX
      (mixedIndex (g:=zF) (i:=0) rfl rfl (before_sound z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def jF := extendPerm jP 13 [(28143,93)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem xA : Known false jF := extend_ok (m:=1407) xK
    (lowerFromFull (q:=1407) [16, 4, 2, 4, 1, 1, 2, 8] jX
      (mixedIndex (g:=zF) (i:=1) rfl rfl (before_sound z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def qZ := extendPerm jF 13 [(54143,0),(64447,94),(44015,8)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yN : Known false qZ := extend_ok (m:=54143) xA
    (lowerFromFull (q:=1407) [2, 1, 34, 4, 1, 5, 2, 8] jX
      (mixedIndex (g:=zF) (i:=2) rfl rfl (before_sound z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def qV := extendPerm qZ 13 [(44927,95),(47999,1),(53119,162),(58239,4),(69503,163),(58303,24),(60351,60),(69567,94),(42991,19),(60399,164),(69103,165)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yJ : Known false qV := extend_ok (m:=44415) yN
    (lowerFromFull (q:=1407) [16, 1, 2, 4, 1, 1, 2, 8] jX
      (mixedIndex (g:=zF) (i:=3) rfl rfl (before_sound z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def qS := extendPerm qV 13 [(43903,0),(46463,95),(48511,1),(51071,91),(43455,47),(43967,89),(54207,166),(58815,60),(49647,19),(51183,92),(54255,8),(55791,12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yG : Known false qS := extend_ok (m:=43903) yJ
    (lowerFromFull (q:=1407) [10, 1, 2, 5, 1, 1, 2, 8] jX
      (mixedIndex (g:=zF) (i:=4) rfl rfl (before_sound z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def q0 := extendPerm qS 13 [(42879,0),(60287,4),(44991,47),(69615,93)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j5 : Known false q0 := extend_ok (m:=42879) yG
    (lowerFromFull (q:=1407) [2, 1, 2, 4, 1, 1, 2, 8] jX
      (mixedIndex (g:=zF) (i:=5) rfl rfl (before_sound z7 zG) zY zS (by decide +kernel))) (by decide +kernel)
def n8 (i : Nat) : Nat := (readWords [0x16ad2728c1ee6b1,0x6a4a0e629062082fff])
def n9 : Packing := (1,0,5,0,0,0,0,n8)
def t8 : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffffffff,0xfffffffffff8278ca9]),(readWords [255,0xffffffffffffffffff,0xfffffffffffe078829])),(0x8c5796,0x1884792),((readWords [255,0xffffffffffffffffff,0xfffffffffff819b865]),0x31b824),((readWords [255,0xffffffffffffffffff,0xfffffffffffe1200db]),(readWords [255,0xffffffffffffffffff,0xfffffffffffec400d9])),(0x4205b12,0x1385302),(0x140617c,0xf06154),(0x808260,0x6740060),(0x430380,0x70e0280),(0x303fc00,0x10b9c00)]
def t7 : List ColumnInfo := readRows 38 (fun x => (readField x 0 17, 0, readField x 17 17, 0, readField x 34 4)) 23 (readWords [860,0xb7ee440d54dfaa1035,0xb3ded810d60f7b0043,0x61eff0e80d75bfbaa0,0x35a6fed280d67bfb3a,0x358efec680d5ebfaf,0x203576feba80d5abfa,0xd20355efeae80d55bf,0xaaa0354efea680c00f,0xd80012c03dc0011c00,0x7f80403003fa0002c0,0xef800834037e0040d,0xf780043402fe0080])
def uL : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def s8 : Nat → Packing
  | 14 => n9
  | _ => emptyPacking
def rN : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def xd : Forest := ⟨1535,14,fun j => t8[j]?.getD (0,0),t7,uL,s8,rN⟩
set_option maxHeartbeats 0 in
theorem k4 : graphValid xd (boundsBefore q0) = true := checkedGeometry 3 2
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem tZ : block xd 14 0 1=true := by decide +kernel
theorem tE : block xd 14 0 1=true := tZ
theorem s0 : checkedTables xd 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block xd 0 0 0 = true)
  · exact (rfl : block xd 1 0 0 = true)
  · exact (rfl : block xd 2 0 0 = true)
  · exact (rfl : block xd 3 0 0 = true)
  · exact (rfl : block xd 4 0 0 = true)
  · exact (rfl : block xd 5 0 0 = true)
  · exact (rfl : block xd 6 0 0 = true)
  · exact (rfl : block xd 7 0 0 = true)
  · exact (rfl : block xd 8 0 0 = true)
  · exact (rfl : block xd 9 0 0 = true)
  · exact (rfl : block xd 10 0 0 = true)
  · exact (rfl : block xd 11 0 0 = true)
  · exact (rfl : block xd 12 0 0 = true)
  · exact (rfl : block xd 13 0 0 = true)
  · exact tE
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseFA : Impossible false (graphGoal 511) 14 (vars 511).toFinset := by
  have h : Impossible false (graphGoal 1535) 14 (vars 1535).toFinset :=
    index_root (g:=xd) (i:=0) rfl rfl (before_sound q0 j5) k4 s0 (by decide +kernel)
  have e1 : graphGoal 1535=graphGoal 511 := by decide +kernel
  have e2 : vars 1535=vars 511 := by decide +kernel
  rw [e1,e2] at h
  exact h
def wO := extendPerm q0 15 [(511,0)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s2 : Known false wO := extend_ok (m:=511) j5
    (plain_low (hints:=13438558465) (by decide +kernel) caseFA) (by decide +kernel)
def neighbor670 (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow670 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor670 i)
def presentRow670 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor670 i))
set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow670 i) graph ≠ bit (presentRow670 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow670 i) (inputs.getD j.val zero) =
      bit (presentRow670 i) (inputs.getD j.val zero)) := by decide +kernel
abbrev TransportEntry := Nat × Nat × Nat × List Nat
def qF (rows : List TransportEntry) (base : List (Nat × Nat)) :=
  rows.map (fun e => (e.1,e.2.1)) ++ base
def q3 (base : List (Nat × Nat)) (e : TransportEntry) :=
  (boundsBefore base e.2.2.1 == e.2.1) && carryOK e.1 e.2.2.1 e.2.2.2
theorem vZ {u base rows} (h : Known u base)
    (cert : rows.all (q3 base) = true) : Known u (qF rows base) := by
  intro e he
  rcases List.mem_append.mp he with hm | hb
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    have hh := List.all_eq_true.mp cert r hr
    simp only [q3,Bool.and_eq_true,beq_iff_eq] at hh
    exact carry_of hh.2 (hh.1 ▸ before_sound base h r.2.2.1)
  · exact h e hb
def wZ : List TransportEntry := readRows 30 (fun x => (readField x 0 17, ([5,9,8,12,13,11,7] : List Nat).getD (readField x 17 3) 0, ([94,91,478,127,251,95,255,3579,28143,18911,17405,4927,17343,17403,17151,9599,2239,1375,1343,11742,1725,6847,1119,1727,2751,2237,18814,2079,2367,2429,27127,7038,11453,48094,42679,42591,44927,42683,44799,46455,58335,58239,68863,42711,42751,42623,42879,58623,43479,58047,54143,43647,44925,44223,44733,64447,44221,64191,44155] : List Nat).getD (readField x 20 6) 0, ([[48,33,133,118],[81,130,118],[32,49,128,81,116,100],[80,16,33,50,116,131,100],[32,83,116],[16,82,131,100],[128,49,100],[48,129,82],[16,32,48,128,100,80,116],[128,81,32,49,100,116],[80,129,50,116]] : List (List Nat)).getD (readField x 26 4) [])) 187 (readWords [0x228721fe8a6487bdb,0x5b21ee9eb487a9b852,0x1e62e6c7fb979b1fe7,0x699c3ff86130ffc9b1,0xc3fede130ff39af43f,0xc6a250fb96a9c37f92,0x870df73e143798a990,0xdbfad6c36f4778f97f,0x6b1baffa666ebfb284,0xbafe5a24ebeca84baf,0x79abcebdc0d93ad6c2,0x72e5be9a9b8fedf5ae,0x3bd4a9b8bfd6f6d9f7,0x99cb67b6a86d7fe5a9,0xb5fdea98d7ef3a635e,0xfce86d6ffaccb4fb4b,0x32d3be2b1b3ff9e66c,0xffd884b3ff1248cfef,0x4d0b3fb42c6cfdf289,0x33f38ae8cfbf08933d,0x7a332c7cf1ca31efca,0xa6c3fe9a1b0fde698c,0x3ef6c6b0fb9a86c3df,0x6a630dfcaf6c1fea9c,0xb07ad704c0fb1bdaf7,0xeca66bbfe8ba2efbe2,0xc6bbdf8b4aef3ca48b,0xbbf1b1abfecec6aff7,0x1af2bfc6a48afef189,0x2bdce612aef7aa9ab7,0xf5e86adfb8a9ab77c2,0x98adbf7a62b5fc286a,0xcff19caa6dc666a7fb,0x484a9fcd65ca7c7192,0x29efd634a77358929b,0x9ce12a6df079a47f99,0x8a7fee8259b7f8c766,0xdfd61d9b7ed6046de6,0xa4a9b6bcd8a6be714c,0x927f149649fb422125,0xfc604495b97991ff50,0xd643fe17c90ef94a63,0x7fe3358dff54c837ef,0x2510df994d637dfa56,0x8def64ba376f2628d7,0xb9de633fe83e0c7bd1,0xd231ed13e0c6fe90a3,0x1bd4728c6bc9bc31ac,0x1258b7f54882dbf168,0x8b6f990a25ee565097,0x9958a21e723987ff88,0xa61ff723207fbd57a1,0xfe793586ff995a1bee,0x13206dfe89619fe122,0x67be16419ce84a865,0xbc0d613fd82984fee0,0xd613f775684ef60c81,0x37f15104d6d1320df3,0x822036fc52a0d3f346,0x832fc8f809bf742826,0xf54f8097f73981ff68,0xd607f773581f7dcc80,0x7bf22e81ebdca606ff,0x725817ee07605f7625,0x8177c888057f11d813,0xfc86601fe611007e94,0x2201f9311007d50220,0x1f3a0c807b643201eb,0xa040079241001e2011,0x77544401d780c807,0x3e00001cc804007188,0x3201be215006f04000,0x1b870c805f54320177,0x515005cd4000171615,0x579810015a504005,0x4d04400fe008803dd0,0x3200ef3088037c8100,0xbc104002e40000097])
def pri := qF wZ wO
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nI : Known false pri := by
  apply vZ s2
  apply pieces_all (d:=6)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
def moY : Array (Bits × Bits) := #[((readWords [255,0xffffffffffffff0247,0x102040c820c0830811]),(readWords [63,0x3f81ff800001f8000])),((readWords [255,0xffffffffffffff04c1,0x40881096109041223]),(readWords [255,0xffffffffffffffffc0,8658654101503])),((readWords [2184,0x245902104218288206]),0xfff800001ff81f8000),((readWords [4368,0x8902432803260844c]),(readWords [255,0xffffffffffffff0000,9007061947908607])),((readWords [770,0x182060608060410c08]),(readWords [65472,0xfc07e0001ff8007e00])),((readWords [40964,0x820208841484826190]),(readWords [255,0xffffffffffffff0000,137436889087])),((readWords [17440,0x410491010901141020]),0x7fff81fffff8000),((readWords [10248,0x20430a040604082080]),(readWords [65535,0x7ffffe000000000])),((readWords [53296,0xc38414021802104140]),(readWords [65535,0xfff800000000000000]))]
def moC : List ColumnInfo := readRows 47 (fun x => (readField x 0 17, ([0,1,16,128,256,8,4,2,64,32] : List Nat).getD (readField x 17 4) 0, readField x 21 17, ([0,50,16,64,18,128,138,276,32,69,258,136,8,384,130,36,256,4,1,68,272,9,2,104,20,48,96,385,129] : List Nat).getD (readField x 38 5) 0, readField x 43 4)) 387 (readWords [8796186083395,0x94a001e900a0a80016,0xb0010a50005c580114,0xa3009c3802154001cc,0x10019280038c400295,0x1806a1c002ad80031a,0x80601b8004e9008834,0x401c6a01106b007304,0x60cb00b0b00049c0,0xf30008638002ae00,0xa8700c6b0060a6e00,0xda800129c0bbc705d,0x1c38243d4120157000,0x7a80002ae057f882b8,0x39c001f10000740175,0x6e0bb488029b9c14e3,0x100715ec38c0a00ceb,0xd8678140002bc000a1,0x802bdcc15d190053b9,0x829a32001373009464,0x2e60008c80005e4,0x10d0000de00010e0,0xe35b371124015ab66,0xac24801256cc904900,0x9ad98489200015b00,0x124021bcc50c09803,0x67981b013005df302e,0x8260001e600004c814,0xdbe0a72090003bc002,0x2136725ec394024001,0x7d0004148002fc0008,0x1902a6dc150912072d,0xf03910640d3be06920,0xc80877c04241900b6f,0x8058832063e78318c2,0x40ebde07510c8003d6,92609011275989586,0x69f683484a4031ed0,0x18094821fe610e0c90,0x37cc018192000fc80,0x1a4049fc02401cc1,0x5d7b0ae02a533af619,0xc01606b5f835d02c00,0xcbf006a05800d7e007,0x40b02bcfc15d816024,0x9f812302c00d3f0066,0x5819ebe0cea0b02ed,0x7c175416024af81228,0x2c0a76f0534858026d,0xe01290b01b6bc0d8a1,0x6018d780c142c0e3bd,0x71215806f7a03642b,0x4ef4024856053f38,0x29862c025e70120c58,0x43ce02018b0437b82,0x18236061f703084701,0xcff0868060093be04,0x820c00df7c06c41803,0x4fb81a0230049fb024,0x260093fa04802c011,0xff408c058061ff0308,0x70091fe04800e0067,0xfc03201d033dfc19d0,0x1a090f784804100016,0x220046ad802c2c0098,0x50007888001ac400a6,0x802819c01616000c3,0x819dbc0cf21702bbcc,0x15e18fc002f480401c,0xaf630574e3814f8e0,0xa638700077000046e0,0x87f8843839c0ebf807,0x503c0181f60c104802,0xbaf615e0500215ec10,0xc0a0000bd000814021,0xf7210e468035f989ac,0x131b002f4800024000,0xdf000904818efc0c68,0x190006f8000832000e,0x78000c2402dde01610,0xcc57ab66bc209033fb,0x419c252053f9829832,0x40cffc06701cb177cc,0x4ba01a52baf615c016,0x71af838a82c0056f0,0x2485800af600484b0,0x1ebc00ca16000d780,0x142c11fe708f0c582,0x1bce10c18b007f9c03,0xc31600df700684700a,0xcff05680601d7be0ea,0x20c02b77c158418009,0xfb80482300e3fb0710,0x2600dbf606c04c004f,0xec024098056fe82b00,0xb0043fd021016005bf,0xa02c02d02bdfc15d01,0xa056bf82b2034001bf,0x206815fde0ae10d,0x67bc03021e000ff8,4503692019504053,0x802e2c008864007304,0x24fa004ba00021f2,0x1cc1000140001f600,0x10480392f61ca05000,0x7f00040600cf5e067,0x50c01d6b66ea248000,0x7d4000153260f31300,0x2240ebf9075034c1c9,0x7b0e402a5392f61c80,0x1607d5f83ed02c0a73,0xf05360580267e012c0,0xb03ad7c1d5416000b7,0x800242c06be70350c5,0x804bdc02411c010bfc,0x8601805def82e8830,0x10ffb087026021bfc1,0xc01d030dfc18500d9,0xa6080209f000e350,0x803821ff010e07800,0x156cc08490075f603a,0x84e00b5f505a05400d,0xbcc46c099043ff021c,0x7607dde83e90ac10f,0xe70870c5806bdc0341,0x1c0437dc218118056f,0xd82b01300ebfd07501,0x6804afe02480d010ef,0xc08481a018df80c103,0x40c3ef061086803fde,0x1e108043f98a1c130,0x1bf310d8262e00974,0x4d8017b0010090,0x778000432000f680,0x4a4001f300006554,0x3cc40000b0022fc01,0x28160049f802302c03,0x1bd0182158033dc018,0x11c038bfc1c601805a,0xef82d08300aff70570,0x46019ffa0ce02c01b7,0xf40d8058090ff04800,0x7410dbf086206805b7,0xe02c407a0038d40008,0xf300dc380006c0053f,0x2605821b7a10c42b,0x26f401085805d7f8,0x2ec0300e3df0711060,0x15ff60ae04c0037ec0,0x18098057fe82b80b40,0xf97f07c40681f77e0f,0xa40700035c00251005,0xead9af09200bbe625d,0x4cc803cc40008c01b,0x7dc0d8118087fe8438,0xb0037fd01b01601af,0xfc0d601d0097bc0482,0x8000f010003e0019e,0x620c04c8001ee00108,0x988056cc004130005e,0xc0000ac000bf000a05,0x8243dc12011c02efdc,0x17411800fff0078074,0x10f7f0874068036fe0,0x1a80d004dfc02501a0,0x63df8319034037ef01,0xb084016ab66b424940,0x56cc00092c00f3100,0x69e015b30000581a,0xfdc0d611b01ffb80fc,0x23a069bf834a0340eb,0xbf07520681af7e0d64,0xd0036fc01881a067f,0x78338418a005e90080,0xbb802e2c0008802a75,0xc150510000eb8000a2,0xa75b3531240012b6,0x60824c043fdc21c11a,0x5ddf82e901da005e9,0xc00017b0010296,0x367989b0036009bd80,0x4a12c11fee08f08e82,0x1f7e10e40d02efbc17,0x420eb00b8b0000a000,0x1fa00002d28017b000,0xd00c7bc060216056,0xbd82b213001bfe00d0,0xe8012fe00880d038e,0xfc1c481a056df82b10,0x24001fc00001d814ef,0x60a684d033efc19c81,0x900dc38000250b55b,0x35a0258012be008a0d,0x2befc15c81a06bf78,0x3584200c1e626004c0,0x63cc4300980397e81,0xc80b070071a800020c,0x1716000060087fc04,0x201d038dfc1c501005,0x45ec2a40b00d9f706c,0x468176fe0ba80d012,0x5fc091016057bd82ba,0x12c0cfee06708e000d,0xfe00700d0026fc0108,0x1a036f781b0418601b,0x870002e00dbfc06c01,0xc0067f803003a075bf,0x83aa0340b57f05a403,0x1402e2c000a7200730,0x400418003ef8018830,0x7f70030460093fc0,0x4801c001ff400c04c2,0x71a80412c0015f00,0x505806fdc03611c00,0xdff806c03a072df839,0x101860097400144000,0x2b66002470007e0000,0xfa086f7843042c0bb,0xee05d08b0803982002,0x2d03afbc1d42180727,0xf83940340abbf05520,0x58063dc03011c0013f,0xc00a01a06cf7836043,0x40c1ef0600840003cc,0x40009c00b7f8058030,0x6cf313602740c77f0,0x63406017bf60bc04c0,0x2eff817403a087f784,0x3842c001e70000c404,0x39820000b0025ec01,0x1096000bd800213400,0x7bf0032068002fe000,0x80d034efc1a4818002,0xfd8010130001fe0000,0xe000bee00408d0007,0xbc000218000fb80002,0x340bd7f05e4060003f,0x600004c00177c00841,0x8067ff033806c001bd,0x216818fde0c610d,0x15fc00901a069f78,0x34842c001ee00008e0,0x14fbe0a620c00077c0,0x418060ff03000700,0xa7fb053026021ffc10,0xe01d02afbc15421805,0x37f829c030001fd000,0x16014fee0a608c000,0x3fc00201a055bf82aa,0x300ebfe07500e814f,0x7e0a640d029dfc14d0,0x1a053f782984300a9f,0xd05401681537e0a840])
def moA : List (List Nat) := uL
def nH (j : Nat) : Nat := (readWords [0x30a206102004e8a0,0xe8c6c0b2eb28da986d,0x9ada8efa1d3d389edf,0xd2bf251de8cb5cd425,0xc1206ddb62a531480c,0x954d524c120661814c,0x53048152605314c120])
def gA (j : Nat) : Nat := (if j<1 then (readWords [0xad8b0aad8b06ad,0x8aa6adc30aaacb30a6,0xcb2aa6cb0aa6c96aa6,0xc94aa5d302a1ab0299,0xc3029603028ebb926e,0xbb906ebb306eb9946e,0xb9926ed306683b8534,0x438b3212cb300b8b29,0x1b012502a524d34f20,0xd34320bb4f1cbb4b1d,0x4aa51cb35114bb4b10,0x1b83051309050aa705,0x7260fcbb52f8bb40f9,0x4260f80b90f4e302f4,0xb90f0ea60f00b90e8,0xb350e4b340e53b02e5,0x3260e4bb70e0bb6ae0,0xbb40e14260e00b90dc,0xc30adceb62d87b82d5,0xe994d26186d26b30ca,0xa2a6c92b02c48b8cc2,0xa392bea382bc9382be,0xa360bea342be8330be,0xa322bea300bea220be,0xa192bea174bea152bc,0x2196b98172b02390ad,0x538cad6b88ad7386ad,0x72a6ad7330a97192a9,0xbb6aa69330a6c2a4a5,0x2342a1b262a0fb429d,0x53309d92629d134299,0xa262983382951b4295,0x733095db0291f2a28c,0xbb708a0aa2880b8a84,0xb8a800b8080daa480,0xc2a67c0b8a78d2a678,0xb90740b8472a3066d,0xcb666ab34a6ab39266,0xb38666b36666b34666,0xb32666b30666b17464,0xbb6a600b8a5c5b8a58,0xe35054a36a500b8a4e,0x4b02480b8244a30244,0xc39640c3663c738639,0x636638cb70340b9032,0x23502c4b96284b9026,0x430424539020db461c,0x53861a2aa619e34616,0x52a615fb461272a612,0x1b460c73860a2b460a,0x3346067aa606439402,0x838a00299700ab6ee2,0x5b30a4119498038247,0xff8ffd3ff0ff6bfd8f,0xf4ffd2fbf3ef4f7f3d,0xd3f72fd5bf3ebcf6f3,0xd3cdbe7d79f3e7bf9e,0xbe76f9d7e6ef9afe67,0xf97fe5ef95fe3fb8fb,0xe1ff7fadfe37f6dfd3,0x7f2dfbb7e6defb7b6d,0x7fb5fcd7df5f6d7bb5,0xdbd6ff5bed6ef5b7d5,0xf7577d3fb3facfdb3e,0xecf7b3d7cefb1ffc7f,0xb1fdc7ef1f7c7bf1df,0xc6ff17fc4ff0ffbfda,0xfd3bedadfdb7daddba,0xffa9ffa7f69fba7de9,0xefa6fe7f69dea5fe8f,0xfa3ee87fe1fd2a5635,0x5602a542505606c8a,0x9505606c8a9605306c,0xda5245302cda466120,0x6d8a3661206e99564d,0x206dc93645206d8936,0x45206c553605206cca,0x9605202e9545c1205c,0xd425c1202e5a154d20,0x6d8a954d206c4a954d,0x202e5a54c5202e1a54,0xc5202e9944c5206dca,0x94c5206d8a94c5206d,0x4a94c5202e9984c120,0x2cd984c120661814c1,0x2054d814c120549814,0xc1206e5804c1202e55,0x34c12054d524c12066,0x1514c120609514c120,0x605514c1202e5514c1,0x206d5314c120605314,0xc1206c8a54c1206d89,0x54c1206d0954c1206c,0xc954c120661a724d20,0x69d9524d206999524d,0x206c8a960d102e9936,0x9106d4a9609106cca,0x9609106e9954c9106e,0x5a54c11054d5248110,0x6c9514811054951481,0x10659a2604306e9926,0x43068991604306c55,0x364420661a3604206e,0x9936042064da154c20,0x2e99854c20655a3608,0x106e995608106c9956,0x810651a3548106e99,0x3548106d593548106a,0x1935481068d9354810,0x68d92548106e582548,0x106a58254810661825,0x481065d82548106598,0x254810655825481065,0x1825481064d8254810]) else (readWords [0x3be919000000000,0,0,0,0,0,0,0,0,0x1c2305002fffec0,0x40580000000000000,2147266564,0xa52000000000000000,201359808,0,0,0,0,0,0,0,4294318356,0x8001ffc827bf200584,0xe0ffbc0c200ffc8060,0xf84dbc8c807710e10,0x2c029d632d006e3250,0x6181d0177035c0f361,0x415300380572c00037,0xf091a14989ae8940cc,0x114815b81a749f0d38,0x15ae10b841d133c21d,0x8b411015c03900d3c,0x101e40490113a0be8,0x1bc00d8dafb5b696d1,0xda1b3f676cdd99b2f6,0x56c9d91b1f636c5d89,0xb0f616c1d81aff5f6b,0xdd79aef5d6b9d71adf,0x5b6b5d69acf596b1d6,0x1abf576add59aaf556,0xa9d51a9f536a5d49a8,0xf516a1d41a7f4f69dd,0x39a6f4d699d31a5f4b,0x695d29a4f49691d21a,0x3f4768dd19a2f45689,0xd11a1f43685d09a083,0xd97a2f25e0bb9762ea,0x5d0b99722e25c0b516,0x92d059cb31652c858c,0xb11612c057caf15d2b,0x49652c2574ac9552a2,0x534a49452824f49c93,0x52624b494925242474,0x8c9152224348490520,0x23f47c8f51e23b4748,0xe51c23746c8d51a233,0x4648c51822f45c8b51,0x622b4548a51422744c,0x895122234448851021,0xf43c8750e21b434865,0xc217422c3204103c0,0x23b0f30f30f2cf303,0x1881930cf2a508f350,0xfd7b06fd5b22f99a20,0xf86392ec6b80ecf172,0xecf306ddc364cdd366,0xc9d172c89b82c2ab02,0xbd8972b6d364b29b04,0xb2d2a4b28972b18b90]))
def gG (j : Nat) : Nat := (readWords [0x6000005c00000,134217732,0x100000000000042800,0,598065675239424,0x2c0000080000000,0x7a03000000001])
def gB (j : Nat) : Nat := (if j<3 then (if j<1 then (readWords [342253605966720,0x4dc9bb864ca24aa651,0x51b2272ecb91186588,0x813743e71a21f3ad28,0xf1d6887813743829b1,0x1c2ccc0d026e860db2,0x62a09ba142cd40a022,0xe85043702425b31112,0xdc081c6a040b3301c5,0xd970e30cb071965438,0xd3281c65ba0a62d905,0x1b6e8201374106da30,0x838d1839765c14c32c,0xa69940536dd01026e,0x809836a046da80236d,0x1811c6a004e3460225,0xb90038d48029660016,0x32e00b9960062ca803,0x365001ab2600fd7480,0x2db3d016d9b22aa6c,0x1215227025d10002e8,0x13ffdffdffe7fefff5,0xff8ffbffdbfebff4ff,0x9ffbffddfeafef7f6f,0xfb5fd8febff4ffa5fb,0xffd7fdffefdf7afb57,0xcffdfddffeff77f7bf,0x7dfaefbf7dbbe7defe,0xf5f77fbb7dd7edff6e,0xfaffd7be7ff3fb9f7b,0xffdff6ff77f7bf7def,0xeeff6ffaffcffe7fb3,0xfb9fbcfbe7bf3bf9bf,0xcbfe3fefff7febfddf,0xeafef7f6bf75efef7d,0x5ffaff57f6bf75f7ad,0xfd5fe7ff3fe9fbc7fe,0x37f17f69573581655c,0x56058d71581715c160,0x58d70581655096058d,0x4158142505602a5415,0x819864530655914c19,0x2645306a5814c15260,0x5302a5814c1a824530,0x694914c1a224530660,0x914c19524530648914,0xc1a46612068598480a,0x366120661944819864,0xd2065d934819564d20,0x26193481986452064d,0x914815364520261914,0x8093645206a5844819,0x5611206a5814819860,0x52054d81480a960520,0x6898048131601206a1,0x74481985d12065d734,0x81935cd2061d734819,0x85c12064d70481845c,0x1205cd70481715c120,0x55170481535c120545,0x70481425c120505704,0x81a954d2068553481a,0x54d2065153480a954,0xd20695434819550d20,0x61143481a750520661,0x414819550520651414,0x81845052054d41481a,0x94c52069531481a04c,0x52065131480a94c520,0x6a130481a54c120689,0x30481a14c120661304,0x81954c120645304818,0x24c12060530481804c,0x12054d30481524c120,0x54530481314c1202a5,0x30480a84c120295304,0x80984c12025530481a,0x32612068498481a824,0xd2069c93481a624d20,0x69493481a124d20660,0x934819524d20254934,0x81a564d10689934419,0x864d1068d924419864,0x910655924419364910,0x6a583440a960d106a5,0x82441956091064d824,0x40a96091064d804413,0x1601106a5524419354,0x91060952440a954910,0x6a532441a54c910655,0x32440a94c910695304,0x41984c110601304415,0x34c1104c530441a848,0x11069520441a348110,0x66120441954811064d,0x20441854811060d204,0x41804811054d204415,0x248110545204415048,0x1104c120441a864430,0x6a5810c1a26043065d,0x810c19660430649810,0xc19160430685980815,0x3644206a581081a360,0x420661810819360420,0x6a553081a854c20685,0x530819854c2064d530,0x81a564c106a192041a,0x5648106a582041a360,0x810661820419760810,0x659820419560810651,0x820419360810649820,0x41a95481068d520419,0x754810651520419354,0x810649520418254810]) else (if j<2 then (readWords [0xaa4bd48b95e6e5,0xcaf522d57a914abd48,0x955e28dc2e946d570a,0x364b851b15c28dc2d9,0x46c96ca362b651b55a,0x28d9ad146c5693b42b,0x451b85928d9ac946c5,0x653b42b2ed98594898,0xac056cd5d3262ae818,0x15642cc2aa1655550b,0x2aa85515544cc2a22,0x6555112a2a87d98534,0x6a8a9856e1482b6aa4,0x7d98523ecaa9266054,0x932a2a47da85118dc2,0x81f6a140fb4aa07da8,0x4e3ed4269f69534fb5,0x967da54b18dc241f6,0xc91cfaa48c7db3453e,0xd2a29f68d14fb408a7,0xd95453ec9a29f6e910,0x6374887dba4318dd21,0x8c6d50cf9748631b54,0x23ed2a11f68508fb40,0x847d534218d9209f68,0xcfcfb407e7d933f3ed,0xd1f0c6e8f863707c7c,0xba3e72dc9eb96a4f5c,0xb267b29533d725c9e9,0xf6d4ecfb50767da53b,0x3edc9d056e4e8fb307,0x47cb93a3edd1c8c6e8,0xe46370727da8393edc,0x9b856e0dc2b626e7cb,0x93718da9b0c6c8d9eb,0x26b495335a4989ab7,0x6e4d1bb30691d52346,0xe5c9a116d4cdbb3066,0x15b3320adc18a76a0c,0x4fb30629da83018da9,0x7bb660b9db705a31b8,0x2d76da96bb6a0b4fb5,0x5aeda52d3ed296bb6,0x60b5db2a5aed852d28,0xdd16146e4b0a374565,0x1b92b76c99555548a8,0xa3745215ba2928dc94,0x8c6e4a4a370532d852,0x9a4c194d56e4a1cb72,0x5155b828aad994556a,0xa12b505155a328aac,0xc1439660a2ab2650e5,0x9328aac1944a54ca2b,0xb744f5db327aed193d,0x764c9ebb064f5cba27,0x4ed4133b66099db264,0xc51b5254ed412bb660,0x9692a64b55522518d9,0x121f6c88cfb44467db,0x9220ada912d6e8856b,0x4442bd52203edd0f8c,0x6e87c636a3e7da51f7,0x2d10fba69479d3443c,0xe9521e18d98e9f6e87,0x63743831b81c74d88,0xe1f6cc6cfb46367d53,0x1b3edc8d056d4695b4,0x632ad53193edd0c0c6,0xe860636a307da5186e,0xa98c1f6e05cfb622e7,0xda8173ed08b9f6e458,0xfb722a7d98154cc08a,0x9f6e850637428ada81,0x46ed409b76844dbb70,0x24ddb21272da88b96c,0xc45cb7020e5b31072d,0x4081f6a040fb6a1e7d,0xb30f3ed2879f68c3cf,0xb721c7d950e56d286a,0xb68c356b4a18b5a30c,0x5aa9862f6942d7b461,0x6c9ba0a3edd050c6e8,0x29936614e5b20a64d2,0x853268c29917414d1a,0x50968d184b454c25bb,0x741031ba086eda840c,0x6d421bb4a10dda3086,0xea984396d41dcb4a0e,0xe5a30772a9839f6cc1,0x8fb460c7db9050adc0,0x2b46a00da34606ddba,0x23edd010c6e809936,0xa04dda8023ed401376,0x8c09cb7002e5a80172,0xd180b96e401cb52009,0x5a30072c9804a54c00,0xc1536268a9b004d9d7,0x826cabc13755809b2a,0x906d9d3882ce883b6d,0x4009ba9c0cdbcb076d,0xa5813672008b98d085,0xd41c05ce026284fe61,0xb67a0edb3d026c5e81,0x172f208b976045cb78,0x22e9b4336ed861b66c,0xedb36026d5b0f174c,0xed8b36754cc318b6e5,0x8a32a6c02cb95f20da,0xaf50605789364b635b,0x6591eda2c906cd64bb,0x30aa6198542ed3a818,0x6994013749e61a64f0,0x4d923022e910117486,0x9b54204d9a1026ccf]) else (readWords [0xc34db2612ad93,0xd36c5869b04c34d81,0x61acdc30566cd82b36,0x2c1598160aca9b0564,0xc582b170c165b85fb2,0xd9afd96c97ecb04bf6,0x4985f50caac2854561,0x4362aca1985650caab,0x286055942a2aca1985,0x350c0a9bc60541e2a4,0x98f1534a78c1a4bc61,0x521e2a48ea1534578a,0x822bc4c115e37488f1,0xb34478d1a23c2e911e,0x34a86f1a14378d021b,0xc54905434480f1833f,0x50c19fbc4c0fde3747,0xcf1b83e78d41f3c684,0xf9e3407d59b93dacd9,0x9ed66c4f6b3607b59a,0x93dacd19ed6684f6b3,0x407b59933dac989ed6,0x4c0f6b1727af1853b5,0xdc9d286e0e9433074,0xf1ba3978dc1cbc6a0e,0x543046ea1813778a91,0xb59548d69b70694db2,0x34a6d89a53608d29b0,0x2694d8233a6a919d96,0x14c2cb0a5b65ba2cb2,0xdc96596ccb2cb74576,0x5b92bb2da95d9694ae,0xcb2a5765532ab2dd14,0xa86e8a6cb7252f1b92,0x9b2dc14956e0a6cb60,0x5365a82950d414d966,0xa5e3305364ba29b25,0xc94d66e0a2b36650f1,0x522378da8fbc6e871e,0x37038f1a81c78da8c3,0xc69461e3022ef1ba0a,0x78d9853c68c282b616,0xe7d98b77cb2da3e58e,0xd0736366f973b31cd8,0xd943596c0fae75e7da,0x2ab3e51559f2a6a923,0x674e7d98a746a95385,0x6d698fb314c7d95a63,0xed4529f6a290fb4b48,0x7da8a33ed2d19f68a8,0xcfb4f447da4a13ed1d,0x9f28e846363407da7,0xa018d8cf8c6e274fb5,0x13a7da19d18dacd8c6,0xc66cfb4b3631b99818,0xd9cb8c6e258636b2c7,0xd87953edd4a0c6c650,0xf975287da3933ec9c9,0x9f24e4d5b2724ac939,0x2185cc8856ce40fb27,0x207d30900ad9c7856c,0x63c29751c30b98e18d,0x8c62d64e2c637114b5,0x878a18d9c4146c6206,0x3631051b88728d8c3b,0xb6621e0aeb0e51b986,0x82c9c2c1612160b270,0x90584849ac241946e6,0x8a361052d548228dc,0x40d566202aaa70051b,0x37f9ac23fc15cdfda1,0x68fc7da97d185cbe9f,0x2a5f46372f87da97c3,0xe54be1f6a5ec736cf4,0x31b17a3ed4bd1f6e9e,0x6370f031b17868cab,0xb8c6ddd4f974ea7dba,0x7418dc3a1f2e9d1a32,0xae6d1957218dcb89f6,0xa1c1a168e07ca8703e,0x52b81f6e5bc2b72de7,0xda96f3ecc379f2e5bc,0x6172de7ca96f4ed437,0x27695ba9326dc9ca96,0xe4e543727295b8fb50,0xda31b86c3edab60c6d,0x5b0fb50d87da06c3ec,0x2b61f541b0f90ad8ec,0xb96b4e54b5a76a1a9d,0x972d4ed98694ed4342,0x7695a1db30d1495368,0xaaa9343b2e5a13950d,0x9ca56876d9b3bb6c5,0x9d3974ceecb567a459,0xb3bb661993974cced9,0x865a4a9b2d5549953b,0x42c8ed986428dd3194,0x6e58deb30c6f58263a,0x4a9b1d55498ca172c6,0x51b2627ac0b1524c58,0xa9372c231b961a4d93,0xd26c5869360c31d52,0x61a45cb0b72e586915,0x2c355ba604add30556,0xcd809b62c155b060aa,0xd4305566181cb30c13,0xd536094a9b0552e982,0xa952c154a860aa4c30,0x146e97ca372bf49b35,0xfaad92fbb6617e5b2a,0xbf5d815fa4a9afbb2e,0x57ca172bf49b95ea4d,0xaaf116d57a934abcdd,0x985ea4caaf516057a7]))) else (if j<5 then (if j<4 then (readWords [0xd65ad969659d96,0x5658d961657d95d656,0xd959655d955654d951,0x653d94d652d949651d,0x945650d94164fd93d6,0x4ed93964dd93564cd9,0x3164bd92d64ad92964,0x9d925648d921647d91,0xd646d919645d915644,0xd911643d90d642d909,0x641d905640d90163fd,0x8fd63ed8f963dd8f56,0x3cd8f163bd8ed63ad8,0xe9639d8e5638d8e163,0x7d8dd636d8d9635d8d,0x5634d8d1633d8cd632,0xd8c9631d8c5630d8c1,0x62fd8bd62ed8b962dd,0x8b562cd8b162bd8ad6,0x2ad8a9629d8a5628d8,0xa1627d89d626d89962,0x5d895624d891623d88,0xd622d889621d885620,0xd88161fd87d61ed879,0x61dd87561cd87161bd,0x86d61ad869619d8656,0x18d861617d85d616d8,0x59615d855614d85161,0x3d84d612d849611d84,0x5610d84160fd83d60e,0xd83960dd83560cd831,0x60bd82d60ad829609d,0x825608d821607d81d6,0x6d819605d815604d8,0x11603d80d602d80960,0x1d805600d8015ffd7f,0xd5fed7f95fdd7f55fc,0xd7f15fbd7ed5fad7e9,0x5f9d7e55f8d7e15f7d,0x7dd5f6d7d95f5d7d55,0xf4d7d15f3d7cd5f2d7,0xc95f1d7c55f0d7c15e,0xfd7bd5eed7b95edd7b,0x55ecd7b15ebd7ad5ea,0xd7a95e9d7a55e8d7a1,0x5e7d79d5e6d7995e5d,0x7955e4d7915e3d78d5,0xe2d7895e1d7855e0d7,0x815dfd77d5ded7795d,0xdd7755dcd7715dbd76,0xd5dad7695d9d7655d8,0xd7615d7d75d5d6d759,0x5d5d7555d4d7515d3d,0x74d5d2d7495d1d7455,0xd0d7415cfd73d5ced7,0x395cdd7355ccd7315c,0x7f7081bbe6d49afa6a,0xa1a5567819a2658993,0x764318ba61d98165f1,0x97625cc16f25abd664,0x58cd5e956755695499,0x4e3525544c503d3c44,0xde932c4b792a149792,0x2047791a5455d12643,0xbd0b141b90404034fc,0x43e1cf453c28ecd3a5,0x8e50384cdcc35e4d3d,0x33d4cab31d4c342fa4,0xbaa2d90b252ba8aa32,0x964a1f278c9ac25dc9,0x3d24188d4226486720,0xf87ff1f007871d1c6f,0xb1b08690195c612177,0x5a615c452d13e44b3,0x11b443f10103b00dec,0x3380bb02b60a102340,0x7f81b7055c118037c0,0xb201cc03e000143056,0xf1142b688aa5ac450a,0xd622e7653987b078c0,0xd73c54ab9e2435cf18,0x1ad7890d6bc616b1e3,0x358f150ab78d4d528,0x54aa143654ea152a75,0xdad32854a99e2a54a,0xf152a478c3cf3c6167,0x9e3073cf1819e78c1c,0xe3c60671e15138f151,0x9b78c1cd3c61665e30,0x732a1ba9878dccc3c6,0x6261e32730f0b99850,0xc3cabc4c651430726f,0x15093789849bc6e646,0xc36322a1a99178dcc7,0x156e238ab6b1d65b08,0xe78a8c54264e261309,0x13094189b2cc43596e,0x60acb6105659382b2c,0x2415954dfe7168fca1,0xa97d785cbe956c9f14,0x34ef8a1a27c50d0be3,0xc6a5ecab62f5399577,0x78c3babc2e1d2732ae,0x539877278dcb8bc655,0xc5e30ae0f1507078cc,0x37a864dbd4170dea0a,0x86fb2c2b73c6059ec9,0x70cd64a866b24c3359,0x6e98ecb72c765b563b,0x2d9b1d96c98ecb50c7,0x65a563b2d131d96618,0xecb2ac7658263b254b,0x1d92958ec92ac76582,0x62b2c0b1594c58a9b7]) else (readWords [6755957049481315,0x4b5a67040841c19b03,0x581e04120b211506f0,0x4200e00c957b18c985,0x45203482640b149f3,0x69029d0a4a2504c704,0xc2024a4f302014cc,0x5ca0d5197044c18e21,0x70ff085841a1151301,0x90e076060439839454,0xa2450bc23403c3137b,0xa81b610305c38cb8c8,0x77d1b70c780c03806,0x603700b3428307839a,0x44a05204260ac137c1,0xdc056022847a09d03e,0xff453c4cc02d05d85,0xe0e060770228a3440b,0xa01e7830078c11801,0xf8b9c4ba20d03a8220,0x6805cb0ad82360782c,0x1d686002ac06d0400,0xed815037c1d3051091,0x80700dc0bd415a0e01,0xc685740502bd004092,0x43022511d82b801d0,0xcf02b843811e0bf0be,0x813e2001f685345cc0,0x503500e4068c090160,0x15a819817e0e786f80,0x4055e02700f803a0bc,0xf687f425a06e09f00,0x35f9d7c75e9d7875d9,0xd7475c9d7075b9d6c7,0x5a9d687599d647589d,0x607579d5c7569d5875,0x59d547549d507539d4,0xc7529d487519d44750,0x9d4074f9d3c74e9d38,0x74d9d3474c9d3074b9,0xd2c74a9d287475d1b7,0x465d177423d06f413d,0x2f403cfef3f3cfaf3,0xe3cf6f3d3cf2f3c3ce,0xef3b3ceaf3a3ce6f39,0x3ce2f383cdef373cda,0xf363cd6f353cd2f343,0xccef333ccaf2f6cbbb,0x2e6cb7b2d6cb3b2c6c,0xafb2b6cabb2a6ca7b2,0x96ca3b286c9fb276c9,0xbb266c97b256c93b24,0x6c8fb236c8bb226c87,0xb216c83b206c7fb1f6,0xc7bb1e6c77b1d6c73b,0x1c6c6fb192c62b182c,0x5eb172c5ab162c56b1,0x52c52b142c4eb132c4,0xab122c46b112c42b10,0x2c3eb0f2c3ab0e2c36,0xb0d2c32b0c2c2eb0b2,0xc2ab0a2c26b092c22b,0x82c1eb072c1ab062c,0x16b052c12b042c0eb0,0x32c0ab022c06b012c0,0x2b002bfeaff2bfaafe,0x2bf6afd2bf2afc2bee,0xafb2beaafa2be6af92,0xbe2af82bdeaf72bdaa,0xf62bd6af52bd2af42b,0xceaf32bcaaf22bc6af,0x12bc2af02bbeaef2bb,0xaaee2bb6aed2bb2aec,0x2baeaeb2baaaea2ba6,0xae92ba2ae82b9eae72,0xb9aae62b96ae52b92a,0xdd0b722dc0b6e2db0b,0x6a2da0b662d90b622d,0x80b5e2d70b5a2d60b5,0x62d50b522d40b4e2d3,0xb4a2d20b462d10b42,0x2d00b3e2cf0b3a2ce0,0xb362cd0b322cc0b2e2,0xcb0b2a2ca0b262c90b,0x222c80b1e2c70b1a2c,0x60b162c50b122c40b0,0xe2c30b0a2c20b062c1,0xb022c00afe2bf0afa,0x2be0af62bd0af22bc0,0xaee2bb0aea2ba0ae62,0xb90ae22b80ade2b70a,0xda2b60ad62b50ad22b,0x40ace2adbab4eacbab,0xeabbaacea79a9c6a6,0x9a986a59a946a49a90,0x6a39a8c6a29a886a19,0xa846a09a8069f9a7c6,0x9e9a7869d9a7469c9a,0x7069b9a6c69a9a6869,0x99a646989a606979a5,0xc6969a586959a54694,0x9a506939a4c6929a48,0x6919a446909a4068f9,0xa3c68e9a3868d9a346,0x8c9a3068b9a2c68a9a,0x286899a246889a2068,0x79a1c6869a186859a0,0xaa7d99dfe7779dbe76,0x79d7e7579d3e7479cf,0xe7379cbe6f49bb26e4,0x9b726d49b326c49af2,0x6b49ab26a49a726949,0xa3268499f267499b26,0x649972654985a60e96])) else (if j<6 then (readWords [0x99f821d9fa046c,0x68900008fcdf90b0,0x602589153f02bb02c8,0x617f96ae0f011c7b10,0x4702ad1020a18d6a29,0xffb4c883c046c0478a,0xfe1c136f683104a35,0x43c2067c18404e219f,0xfc9901060c2041c4a3,0xf060df84b40800913e,0xffa61909c80c200bc5,0x16ffdf823830806f,0x1415fc2b5162053691,0x7e6fcfa24c20271000,0x5fae490101653835f3,0x39ffa623d10027a64,0xe8100587f7c0001bf9,0x7a610096280803ffe0,0x46cd27801594688e98,0xbc12344c025a7003,0x5f00baa097bb115e62,0x7be14b30baac6501e0,0x86f7c9c0c978000809,0xc48bf87db188105a1c,0xd7fe3d4204158827,0x9c33ac4082f1001737,0xd02041688020fe160,0x8094c01ff690ee320,0x813563fc9c2888105,0xa1c1cfffb963040812,0x44821f37c501048881,0x958beffe685190045,0x6837fdd60387081003,0x89000000005f053fcc,0xa241eff66f38548608,0xf82619e61e9b34d3f4,0x68e00a16d14428ae78,0x3ca0cd2d09d11cf073,0x140cb30f3444fbf988,0x157c0e7088e78382af,0x81cd10fcf06300a616,0xc8462279f8c02ab443,0x21e128a073f1b3ef01,0xaa1c801bf837e43a9a,0x6b885fad43c181,0xc54bbeae9adfc18bba,0xe09a8742ffec130946,0xce11fb0d0251b387c2,0xbf61a049c6813d6aab,0xf2d1200dbb91b3491f,0xd32d517589d5a71fe4,0xcac2f185e4457f2cb5,0xdd6299a113fe809979,0x8819a400f921e6244e,0xb08162b7f8bac85e4c,0xe9257f7733b3414eff,0x17590bc99d279f8f26,0x94e4404ad12cfeaf2d,0xc2c36f1cae8d240c,0x933f75d86220849aff,0xf812050022106a3ee5,0xf330a102ab7fc5a071,0x8020822275f8f17150,0x420889b87e3c2820,0xa73e1882501103b481,0x7ffff0ae06c501103b,0x66ffec2284941273d3,0xfb3025011483513fd3,0x808604002144c503ff,0xba2003190d3f1c485a,0x4324025eae9c044400,0x213ac58dff1301c4b0,0x922ff7602184e20962,0x24000000003fc3bfb7,0x970009bc00f100de0e,0xf0b440057f0e847175,0xa21f80c20150a6fcda,0x28881042200017fa6,0xdb970c2fcdf310000c,0x3c448c81c409a69484,0xf414b8aac4a603a432,0xc6c61d31c986324511,0xe929346509a8162060,0x870607c0d606116c88,0x191348da45d25a9094,0x92816c1520a8053c2d,0x401ae1d689b46614b0,0xa5052791a0e8007aa5,0x8c30af0e0582ec28c0,0xa2084c80652a14d94b,0x58dacb562db35da16c,0x2461a0671b0e89d84d,0x36a9bf42260b500b04,0x481c7a9396b589609b,0x633d278c282c205d01,0x1da4c6020b0d22ea1c,0xc6c84ed1ee80c2e015,0x6d57ca874a760fb135,0x92a9840df0b9051014,0x82ab5720b09961590,0x8f886817472b37c024,0x8e58e0f41185794e66,0xed074e3042ea114e04,0x846f0200ca06380630,0xcb00d83a917884690c,0x951120d8778a366ab2,0x282d943be11b08f019,0x442623d06287ec220a,0xff079880c6d08e12df,0x5e0dd07090b022d01,0xed07c32d8ca8b740b9,0xa806a0c4522a80d50,0xe614316a8f409c1430,0x4740061670a30a8855]) else (readWords [2271,0x904283c4000000abf9,0x39119a662980000000,0,0,0,0xcffd08b59234a0000,0,0,0,0,0x1dbcb1665b8800000,0,0,0,0,0,0,0,0,0,0,0,0,0xffe4d7eff2524,0x880000000000000000,0,0,0,0,0,0,0,0,46179355041344,0x694eb0116300000000,0x1e0f0a08946a870,0,0,0,0,0,0,0,23620534788,0x70a01d7e3fc3344962,0x26c0031ffabfc400,0x746100822c00000000,62455588,0xeac40ab40000000000,0,3931848,0x60c202710000013ff,0xfebe900c1840028b00,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6021161,0x164d068632a0000000,0x13ff57fb60290460,0xf7fc0005393f006,0xc531a00000000010f,0xf829f9e6940c91e000,0xaffd3830a8b668d1,0x60013ffa603601cfa2,0xb4500000055f900829,0x6054aa000000001eff,0xfc852172c4b0093c8a,0x5fdcf09c154574e009,0xe17c019806b4f6396b,0xc03710571953066200,0x23ffd96277022b1,0x4071f281c064006750,79096584189739,0x10f1a000bf829f1b7,0x930049140000000025,0xff07be19040c31cf7d,0x48d568e52cbff6a6a2,0x3bc650e0033db84bab,0x22240067e0fd7882,0xc022c4c7edc0c302d9]))))
def gH (j : Nat) : Nat := (if j<1 then (readWords [8068216350920704,0,139125455,0x80b68a000000000006,0xaccd2000100f80000,36,0x1400060be000609e00,0,0,0x214a00044940000000,0x607603580000000,0x641200040660,26134708224,291,0xd000041b8001021000,101736448,0,0,0x168057800000000008,0x3f0000000000120260,0x500000000000000000,0,618530,0xa4a602d000000040b8,0x44800000021400002,0xe4000000184100000,1586304,0x168000000000000,4536584976203776,0x18068001b2ea15a000,73570522074316800,0,0x817800000020040,1240901103398,0xa20000000000000083,0x880000000000000000,0x520001a398000150,0x813800000a800040f6,0,0,872576,0x34000000000000010c,0x1800000000010250eb,0x8000000000062cc000,5033701670912,0,9,0x4fc122000009000000,0x1a3be03c000000000,0x20298330000000000,0x100940018230000000,16738,0,2151153668,0xad8000000000000000,0x60f2000000180,0x892b40000000000204,0xa00020d80000000000,0x407400280000000000,4152,0x848000025581660,0x2143009a0a000000,0x3ac8000000000000,0,0x32b80000000000,140050640,0xc0800c00da0000,0xcd68001846c01c8,0x1c8002000000000000,0,0x4f5c0000000000000,0,0,20021688,0x103eeebc82380000,25952256000,59904,0xb7019000000048b,0x600000000000000000,0,0,0x614400041460,0,2129408,414195908608,0,272826368,6,0xbb829331aa5680000,0,3183616,0,0x1843800023c0000000,0,4,0xaa000000000000000,25840587008,19516335591424,0x95e00000f8000000,2058,0x800000000000000000,0x85860a200000000004,0x2e000000000000000,1055232,0x8058000baa60ee00,0,0x82200000000000000,28991054434,0,0x2c8000a46a0628,0x4f8000849800000000,4673329430721,0x2288180091c125021a,0x8803120000b00a200]) else (readWords [0x401f853000084,0xd8000000604c000000,983040,405177396,555661787136,0x1840000000000000,8678014976,0,581,0x200060400000056811,0x800131200000050000,0x94e00000000000,0x104b603600000000,19584,0x4f49847c10800,0,0x800000000000000000,864237077397504,542638080,71476845740032,0x84b800000000,0xc6e030c15600,60429,0xe00028a800000018b0,0x80000538001bd40000,0,0,0,2176000,0x40e60000000000000,2117,0x800091600000000000,0,0xfe000000000000000,0xe0000000000000000,0,0,0x224000080c8000000,72831650223882240,1628438528,0x1998800000000012,0x520000398800000000,129,0xe800010e8432000000,34340864,0x22f800000000000000,0,0,8753512448,2153472,305114485338112,1171049676800,0,8884139851782,0xc6000000000000015,0xad000000000ce00060,0x7c0000000000205c00,0,0,0x24d84a01540000000,70914,0xe800041520000001a,0x30206a000000000040,0x980000000000401800,370538774004749,0x400000000000000000,0x2f5a832a11584f0020,0x144e2c890dce95042a,0x800b2e124020a69f0,0x4ec04000000000000,0x185ae092000000000,4506898172471296,0x64380000f4a000,136937472,0x854000104ee0e00000,0x22200f400000000,0,562036736,413944537088]))
def gC (j : Nat) : Nat := (if j<3 then (if j<1 then (readWords [0xd308fe9547f4cc,0x3da54ded352ee9a177,0x4d03ba651dd2e8ee8a,0x9774cc39a655cd330d,0xe9956f4c3b7a5cdbd2,0xa6de9a96b4d2b5a681,0xad32ad69946b4aa35a,0x2a5ad14ad68956b4d2,0xb3a6859d330ce99567,0x4c133a6059d2a6ce95,0x267498b3a6617d32ab,0xe9a85b4d2ada6896d3,0x30b69a8574d2aba68d,0x5d330ae995574c9aba,0x60d5d352a69a94f4d2,0xa7a68d3d3429e9a04f,0x4caa7a64d3d2a69e8a,0x94f4d125a64d2d2a69,0x69524b498a5a6a51d3,0x468e9a0474c9a3a60d,0x1d34486993434c121a,0x6a4fd34a7e9953f4c2,0x9fa694ed330769823b,0x4c09da548ed3506e9a,0x5374cc1ba64cdd2a66,0xe9a22b4a915a68c6d2,0xa6369a8174d08ba694,0x1d3460e953074d1803,0x69706b317c187be4b2,0xdf258ef82e374963ba,0x4b2d9258eb9a855b59,0x8a9acad4d64aa6b534,0x8da8a06d2d0368a86b,0x3143595a1ac950d692,0x76b433b4a39dacc4cd,0x66256b2f2b59595a4c,0x4ad66246b272349891,0xa49c836a636b2b1b5a,0x9886d4c4e662219531,0xda2846d440d66201b,0x52fc1977dac9bf061d,0xf82e8fe59879acc3d9,0x64decb08f41737a0b8,0xbd9551ecaa6f65517b,0x2a0bcd6a5d6952e8da,0x571acc38d655c9b08e,0xda76dacc36d655b9b,0x28dcd846dad4b43695,0xacb40d359469a54b59,0x6a19cb4ace5a2672d0,0xb3966196b30ce59567,0x2c8b396099cb02ce58,0x66aa9b375499caa2c,0xd53167254b392a19c9,0x4ace4986724ab2368d,0x81b42c0da85c6d2ae3,0x68576b30bb5955da4a,0xaed6a166b4ab35a259,0xacc2cd6a156b46ab59,0x855acaaad64d56b52a,0x35a94c6d4a6d65536b,0x269b4a94dac9a4d6a5,0x11b528b59346ec122d,0x6a4f1b4a7b5953c6d2,0x9cd660ecb00755533a,0xa989d96a0d1b506e5a,0x5346d29b968cdcb306,0xb598372ca9b964cd6b,0x266e585372c19b9600,0xdcaa66dd52372a81b9,0x4c0d6b505b5a9286d1,0x14d648a6b424b5a521,0xad40ed54c76b5230da,0x319ac98cd6a451b502,0x8da115acc0ad69436b,0x50135a509ad482368c,0x16b2a0b59305ad4803,0x68c06b2605d82000d4,0xe0565ef8b09681a9b2,0x2b25602a6b0153481a,0x98c054c406a610352f,0x95977debabcf5d1e7a,0xe6f3d717aca13c02a5,0xd4328d80a9698cc334,0x54d9b2a4cd131642d3,0xae269970352a00a950,0xd4a602a530152881a,0x93c0549ec64cdb2a46,0xe15134cd11806a4a2b,0x2e51996296c89406a4,0x62330301a9152c98a5,0x68c44b4a1a9a8094d2,0x8406a4123300959704,0xccb027654143280a59,0x3054c90206a402b2e0,0x2194012c980a6480ff,0xfffeffcffbffaff7ff,0x6feffbffaff7ff7eef,0xfdffdfedfddfbdf7de,0xfddfdbfd7fcffbffbb,0xfb7f9ff5cd605c5605,0xc16059160509605056,0x64530605302453066,0x1206512064d2064520,0x6112060520601205d1,0x205cd205c12054d205,0xd20505204c5204c12,0x2612024d2064d1064,0x91060d106091060110,0x54910541104c9104c1,0x104811065830644306,0x4306602064c206442,0x6042054c2065c1064,0xc10648106081054810]) else (if j<2 then (readWords [8165190436797532,0xc4281508341160905e,0xa25246a45614632208,0xc4b43008f817409c09,0xa2d21924f069c18a1f,0x49044a2605882b80a,0xa07a09a2ec0b83b21a,0x59c31c2f039c06c0d,0xc1703e40a05d808415,0x41604340842802c401,0x80c034e2003881e40e,0x37c1d410c2182780e,0xe1bc1ca2980581640c,0xa12a19811a14c08a0b,0x60f405c13c0a60702a,0xc10a0680d024801c02,0xc01c03c04c00ad375a,0x4eb45d683acf759ceb,0x35d663acb7594eb25d,0x643ac7758ceb15d623,0xac37584eadf55b6ab5,0xd569aacf5596ab1d56,0x1aabf5576aadd559aa,0xaf5556aa9d551aa9f5,0x536aa5d549aa8f5516,0xaa1d5316a5ed4b5a95,0xb5296a4ed495a91b50,0xeea19d42ba847506e9,0xc65384a6f94dd29b65,0x364a6b94bbe941522a,0xa35d44ca862508da10,0xb41f683ad06da0cb41,0x767e5cfc39f013de27,0xb84f689ec13d627a84,0xf489e813ce27984f28,0x9e413c62750ce999d2,0x33a26740ce799ce339,0xa6730ce599ca339267,0x20ce399c6338a6710c,0xe199c233826700cdf9,0x9be337a66f0cdd99ba,0x337266e0cdb99a7734,0xce695cd239a37344e6,0x85cd0399f733ce675c,0xce399b7334e665ccc3,0x997732ce655cca3993,0x7324e60ecc15981b30,0x165fecbf597db2f965,0xeecbd5979b2cfe5684,0xa2d93692472433c7b0,0x8e011aa230cc5bd8ac,0x313c624c444e87f50e,0xc21b3c3148571090e0,0xf0c18a82670322026b,0xffa7f6afda9f91bee6,0x7d50f8c9ee4bd7f7a7,0x8f40de62bc627814ef,0x15dab3af57516e89dc,0xee397c7258e309c15b,0x7af6ea6db1db2db5e9,0x6a96d37da47b432679,0x4cda198332a86478c7,0x158b7b10f6172c1b98,0x132fb35eb8bc2d762a,0xe6f5c56b7616bc2d2d,0x59beb1e560f2baf56b,0xaabe1557aa6253eaa6,0xdd4b6291c518ca17d4,0xe27b24e909be13632,0x6764c7897f92dea572,0x4a6893fd266249948d,0xa90ed1f8a3a746d28c,0x5115f22744468879d0,0xcea14041f482a50269,0xfeb3f387ce4f641e63,0x3bd076d4ebf9d533a0,0xe7354e511c63386e70,0x14dde1b65361c6a88d,0x389a1f3370659cc8c9,0x8d1311460c8bee9796,0x2e965bb0b5696582be,0xe56d0ab8952f29ae52,0x24a2513fe27904de89,0x8d92e3252e49248f51,0x1942288442084e1048,0x20183e4c7a20ed71d0,0x438dc6ec8d8e1a5433,0x446378c1316fa2c405,0x670a84148a28004df8,0x99b1266239444d0863,0x10641fec3e1077a0e7,0xa1c4036786a80cd418,0x882e4059a0aa4143c2,0x660491089c106c1e90,0x38e06a60c741738293,0x4ba08240e7019b029,0x804400678094007800,0x34d4e1a6970d3097e,0x942bf4c3d9a5cebd35,0x1569a5ab4d155a662a,0xd32b56992ab45455a2,0x96ad145569a9a74d05,0x3a64a9d2a54e8a9a74,0x4953a6927d3473e9a1,0x9f451cfa6626d3512e,0x9a7974d2cba6865d33,0x12e997974cacba61e5,0xd1512e8a59744c4ba6,0xa24d34726998934c9c,0x9a54e4d3311e9878f4,0xd4c5a68e2d34116998,0x8b4c9c5a54e2d12716,0x9a2874d0c3a60a1d26,0x30e998834cc3fa64df]) else (readWords [0x27f317c0c4100a,0x442dfdd0d2280dffe2,0xd584088135eea40164,0x70197f03001883e0a6,0xf524fffd90cf102008,0xa279f64531004b43e,0xff3ea88241239fce44,0x1004b4381fef488002,0x1698dffbb420882008,0xa249ffab1104012d0,0xf3fc4820a24817ffd2,0x1801004fc45f999882,0x27038005ed9d96b29c,0x1eab0e002db6650e28,0x7be0e717b2cf593,0x518b440cf5932e141e,0xab0e000e36650e2b3f,0x9dbe68466caa3567f3,0xb7cd08cd9456a260d1,0x536fcd30e0d1053ee,0xce77212279e0b5bbac,0x5431bff5a3f7006569,0x86241ffe1c220195a3,0xa22bf1f1c81aab8b42,0xc42c7b42eac92b10b1,0xed0bab2493f07bff76,0x804a16e3a452c42c7b,0x42eac926ff1fffc04a,0x67034ad159f0050b7,0x5619a442f4744983a,0x4bdff48802418e01a4,0x5a9133ef1a3217404a,0x3aff302b8639553b4,0x332d85a150869b7fff,0xc0ce6940c301a3a8b1,0x33ae7a3217044a8702,0x7043823842cc0f16d1,0x7c16fc20a201768b04,0xf04ac14517433cacfc,0x8606810b33a181c7c1,0x554b348c5420d845b0,0xa42ef2872644a446c4,0xa948647242147d4a81,0x3eaef0b28c488c49c4,0x7b1370ffa8513686da,0xeb90b22e25a28508c0,0x6d07fc7b218c1a0ada,0xb1a96aab65a66b6850,0xb917717f68964667e6,0x2963d61946011c6d36,0x7369715717941a11fa,0xd621b1671662c344d1,0x6533820330a6bc160a,0x4f17e33b0cb3016933,0x3917a1784201718f52,0xb2af17d8828fa3320,0xdf3314c217b0de1801,0x1616e2514526ae03b6,0xa26f86d210d20a2d32,0x900a000da731144611,0x1b8751069059068650,0x4808a0085288545585,0x6bc48c5114844284c1,0x82c2b4b715dc05c0e9,0x3485b80087b82126b8,0x42eba9d08d69dc8d1,0x6911311272d27e62e0,0x4e1091470200111642,0xd51532fd4d045c10c8,0xb316344843b4404658,0xcb6202fc8a4c7247c4,0x624310c644bc6c2452,0x228aa41f8944686180,0xc8a9511e46e8801202,0xda61b0e81212812c03,0x20e111911811daaf2,0xa1aa1abc2360b041b0,0xcd64a2fb0c9a1b81a8,0x2c4f44f30e941d8091,0x174f18400400650542,0xa283f11143f0e244c0,0xdd110c15c47c63c62c,0x7d22d0b8a7aa6b0e3a,0xae01b10f4806c31000,0x800c40918c10ca8514,0x948a3c1e42f82f46d0,0xb70a7a88c5f45f4634,0x3ac5b2962ab2012952,0xb181d84d0ce60243c4,0x352882d78660b4a930,0xe703040760b8184d14,0x9f86e83c49e0278480,0xe502b0b5441c220790,0xe405506a267a670b6a,0x4a06606e25324a4660,0x188ac0c7075081841a,0x22c1f0a5400209a890,0x9aa7e2c50822ad4a00,0xba22540da188610a6c,0x3a0bb23d060a8709b2,0x2600700f01a0908108,0x7f08e427c2342241c2,0x661a84ea3244ec070,0x1600c00500e830c110,0x760560712020992328,0x2262663604d6250740,0x98a1a297061423c64c,0x41842417077a0f0848,0x60a0206f40f0788472,0x12a33a5a62d03c0352,0x73052070451c4cc3fa,0x5083541805720f0922,0x7a36a46229250a536,0x33612a3da030098280]))) else (if j<4 then (readWords [0x7219fe1f007f08,0xbb477f7fde5f08284,0x286acbd5dce06080e,0x38068a9006ff8ec55d,0x8e204021aa81efe4f0,0x3bea90c0cd1e4049c6,0x85f80139fd76148a7a,0x7fff240b56da0601f7,0x52017238dfd5ff86e9,0x594189335c80bc8e43,0xfc1ab202c9804071a9,0xead39ed40d59e2f47c,0x49415555401cea5193,0xf01ac183187dff14f3,0xf1208092b7be9789ea,0x9044e96efe1f0d2104,0x20080a2b7fc53cfc48,0x2024abff7ef0111015,0x5f9fe6022022adff50,0x104a0937e660444a5,0x27fff30111294abfe3,0xf6b788100405129fff,0xf56bcf410103356fef,0xf3ea090440954f87bf,0xfa935220802108b47f,0xdffd328c88820089e2,0xc001ee87f43080085a,0x8dec79627c482a24c1,0x64fee37c4384010b45,0x7ffeff3100440442d,0x4f71bcaf3069881020,0x22aabf51fd20f3020,0x822248fd6dbea0840,0x40045153efff37fbfe,0x7510410054317afe9e,0x847ffc10941040115c,0x617ffefc7483a22020,0x26bc7ffffe410a0468,0x82100405180f7ecf37,0x8048fba41431080224,0x8ff7fff1f1ee43848b,0x384011446821f829e0,0x87ae9fb02404122008,0x4991dff50010446927,0xfe7ef01111955f9981,0x1099497ffa36440001,0x109b61fffcc044465,0x3bfea00208152771f1,0x5d4004110265f99811,0x12949fffcc0444a535,0xffb2742000202526b4,0xbffbc1349040040044,0x75487ff292b8208008,0x8e6a814f07800057,0xfc42000020088e3ef8,0xff9c4446525fffff42,0x364601010bb6025e2f,0x5fe4a0000080237,0x8e00affff3a1000101,0x11b673a3c13cd4c370,0x633115deb0f5805b76,0xe686d4025fc8b72f56,0xe49aa1deafeb30e014,0x65b66522309ffb4353,0x3e404641b2117e7f0a,0x449742b0caa15f97b,0x435738a06b3c4c3f97,0xa3f550879f0520d608,0xccfe7e6f346264ad27,0x7382cafdd484832427,0xaa77eef02bfc9dc641,0xc6e2dc67054414dbb,0x9dc83893391e890556,0x7e695087245d4d45df,0x99d401de8fa8749bb5,0x9cee42c613fa93ad1f,0x209128b11404dff010,0x629a369dde8f93f888,0x6568622660858f617,0x754963e4d64b5d27aa,0x68dea5dff2d5fc7f01,0x2819c0d43460f10b1f,0x449b02483fe0671172,0x180d20454bff35e257,0xdd3b41314affff1f0,0x3058d2b4c0685a3002,0xffe7eff12ada1da688,0xa01116fcdf9099c6d4,0x58a5bd8f7d6292e9a6,937884796,0xd93cb508e37bb46268,0x30e7f08d678b33e17a,0x1ce6948a637e4f050d,0xc70030c1aa759011a2,0x6c8d27afcbd020113e,0x9266b6ffaf00f6c32f,0x66afd20ca005b80000,0x9d0dee164e4c901ea8,0x9fe6fa7a84184001c4,0x811fe36d9e51b89009,0x16b1baffe546200af,0x20212240aff5f013a6,0x36d2e32024a37dfc0,0xe8093652d81900e518,0x15ebfe014b403b43d,0xa001b7eb8018fe14c4,0x2e342901946857ff84,0x7ff0f000cc00b0000e,0x877f6c20026ee0023f,0xfc44007bcc5e835520,0x328f0be078358f2008,0xa9f9f003f4e3671001,0x889b7ece8009040071,0xff2cce0620802489]) else (if j<5 then (readWords [0xe20022f3725ec4,0x4a491013ff8000020d,0xf1000ae2013e6d025e,0xc44e59500006ffe000,0x5aa749ad2c1e1495c,0xe0858006db409c4e00,385859584,0x1be28725d2f07a5c0a,0xeb42519c000000000c,0xffe9c10821e9a6a002,0xad9cae43c426539bdb,0xe77b330a506c67aa42,0xaa0000000008fffeea,0xd9ed349b2733350107,0x29cffa33ca2e6212ca,0x7cc519cffa73c1c86,0x212ca46cc7198ffffc,0x5f0fb218842098c9ac,0xf51d27ff8189810c10,0x140136aa00000b7d5f,0xb29d102264fe000000,0x17e62950c2a4000025,0xf77eca744089dbf4f4,0x99e7314a9e54025f66,0x9c3fa8c4a74248a034,0xfcbf36fb94308a5484,0xab000024fe47c2a90e,0x9951060805157d9e24,0x1f0a5a3594760e0013,0x5937f97b380a534304,0x24aab1fca4dccb242,0x21840594628df013fc,0xb2e529015338808c8f,1511601823591,0xe836971013120afabd,0xb420d64ce2026a2dcf,0xa0ccafbd880274fd84,0x9b39ff1daa01d5ac93,0x6efc563b5404bb59ad,0xb6578a0000718024fb,0x44580019c687e9fa45,0x2105b8c804de270807,0x964414fffe53766eec,0xef60e100711ba7fe90,0x9d46191012d4161fc5,0x53d9180046a6fc2bc7,0x230173449ff0675d99,0x2274d0f9199be9e008,0x340c4202523a5ffba9,0x1488c9c9a29a8a2d0f,0x14fe8e7183334e0ff,0xfe68fc550aded01201,0x20316381fcf1db2085,0x2d2d81901a51c00000,0xc7fad825319100804,0xc56957ce7f00a5a01d,0xa1ef2002380006ffcd,0xb100c80328906bf0f1,0x64b89ef744280a88d0,0xfd3a7ff00122440596,0xb57f8b92782b95f842,0xce2027a3d9ff0ffc4,0x10000c800280000781,0xef641000acb33fd5fc,0x7c35654b0354b31462,0x401248e3ff7370e551,0xc6c189009c68008ffc,0x6bedeb103120009013,0xee090008ca2be0b600,0x1bd802837712a40044,0x78000b7fff80350530,0x55f8d500b71e003bff,0x1e4c78f02013200120,0x5196cdb3812acc001,0x6fe087bf2eec13f1e6,0x403cc771e4f38d02c6,0x47c02bd483dfc1e006,0x40d5c582015e331fc8,0xfffa45b3b59058202,0x5e340017c1cdea8b67,0x707080658d03ae376c,0x62ba11115c4019eb3a,0xdfd376c934e0bb7d80,0xb36ed7f07dd77d00ab,0x36bea2100d28e05bff,0xc001228ecddd9c0e49,0x201d1214f039a59318,0x9f3680414602da3a7a,0x59333e6954800a4683,0xde0fa1936dcfe20009,0x179fa53a36be41600d,0x9adeffd6f22e9c2007,0xaa0000029fc1af03be,0x4f30b2cd05d4780065,0xd085f690cc98007aa9,0x7ffcc2ceca818e01a4,0x50bf0b3b2a82380691,0x31ffffccefcd583270,0x22b6774c74dd832702,0x3b5cbff91aa80c0120,0x80378b87ff77f11201,0x81812080038d2ffbf8,0xcadd709c068d55fdff,0xead81832703cb5e3fd,0xbc12ffdf6e95424100,0x6d1b9763e34be80b80,0x30e00eaac02ff87901,0xe00001ff7088401247,0x175cb8e0a0c19d0806,0xedce07fff571047180,0xc720809d8e67ffa044,0xaa08e0324487e5f286,0x40018f82a5ac14f03b,0x13dfd43c954241000]) else (readWords [6734424715413,0x44aa40000000000000,0,3908221,0xcbf2c2100ecd400000,30064221551,0x98b308010458000000,0xdfffc9278bff824,0x8110248018d0500699,0x300000000000047f18,0x6f655b6d759388e0,0x7d483aef17f42580a3,0xc86041d200823c1e0e,0x2a76ec09254829233,0xdffffb7aaca4b0328e,0xd39c42001e411ffff,0xc50979cea0c08e1ccc,0x4202d643de2843078e,0xa644021196406f909,0x3b6c96570590e00000,100655157,0x5a7e307eab1f1a1004,0x200134a001bffedab1,0x6a006880000000000,239,0xfff3e39c0fcee13780,0x89150112e400000000,0,0,35,0xfff8386267fe8f1012,0x4a0105c8000000000,0,447,0xfb75fe32842460c000,0x40109122000000000,0,0x1dffc5efed5880efd,0xe6f800a5c98000147f,0xcc0c2040c696a2e8a3,0xae013ff814007a582d,0x35a583c217b36001c6,0x9040d30000010f880c]))))
def gI (j : Nat) : Nat := (if j<2 then (if j<1 then (readWords [0x4cc2da88830172,0x831e002d02b281d382,0x2485b0ad35c11a443b,0xc1bfc2fa80de2ec2c2,0xc98298826ceabb815c,0x24ccc4e88e80d2582,0xb9083602635225c116,0x851d01b41c4d0577c0,0x5ec2a199d0014381e9,0x5c4fddfa8176a60883,0x1c82f8057841ff805a,0x122429d08f00160c2,0xc0400bc4e390f742ef,0x8016c1860729c19dc0,0x1ac0ce801800a0c266,0x810c8333914e99fac0,0x3e42b61da642e1c86a,0x992e402ec11fd1af41,0x3ec2c6c86f00f4031f,0x412f42930000000082,0x1d001c826f0000d9e8,0x81ac10ee8d94c934a9,0x30000000000008076,0x42c39e690000c0,0x9842614180d1ff0000,0x49940000ae81df,0x601e6000042320000,0x81a9c2010950821300,0xae424e919741bc1170,0x81ad902bc274c3,0x142f409f00000c147,0x20e2532813a000001,0xe91a48316000059dd,0x403b81a1c1dd40f018,0x4d1f0ae9592160d93,0xc107018a81c8009dc0,0x3100004abb0090504e,0xc50b4008c59b9db981,0x2e0b25086c1a1a0005,0x1a5d5048000000ebc1,0x7321e8850140ed9f2b,0x8525c0d1c899904a4d,0x981a6806841460000,0xc26742f240d4000080,0x860515117108419153,831707165440,0x325000000110000,0xc2dfea0caaea66c142,0xf642530000000042ee,0x84fc893b00b3408ec1,0x330000c89642880152,0x8ebbd0ea000000006e,0x1300005172cd372226,0x401400001038494825,0xf800000000492504e1,0x42e00000000045,0x38461b0300c0f71918,0x31500b601de02cd52,0xe4414e5f0f00c34105,0x4132c1b2d0605cd784,0xd3c280d93002308038,0x1c91e4a0000000001,0x5400c8000002dba305,0x921f017f0a00405282,0xd5d0500000ae8c9100,0xc11182e2000002fd00,0x37c2fe480dc1350000,0xd808fd130b0000c8,0x1ecde3c007d02d8268,0x8089804f000046,0x37427d00a7c318c167,0x81af000000000000c0,0xe0019a863a42dec0bb,0xc144c24f405b000049,0x7526d52c3823c2e06,0x9002302010a881c05,0x4a2502014110031026,0x12e0b453e27770403,0x3e0011803e07000209,0x10004f1c273a16170f,0x6b0100090104001d1b,0xb0c12230513002001,0x2e1b0812000a100103,0x5c4d0d070e0013043b,0x32e1e200739100200,0x800051a3147000e,0xb2501000101020105,0x803112300100a02,0x52202100217241a0f,0x909180001020046,6764300392033845,0x3a250c152207430003,0x1403141219020028,0x5101708000f0802,0x20001e43090a1e0e1a,0x90a0f1006013f0601,0xb10390e3f00091e,0x61901020613030023,0x7000507002a0f0900,0xb03010a1d0b0d6009,0x4090520300e1e17,0xc670409030b141707,0x30b01261c000d2a06,0x110331050702050410,0x1a0d0f040300380b01,0xd0206131813010304,0x505050e1805030017,0xa00190806130d0829,0x41a4e01010009063e,0x219220038001e0b03,0x2d01051502200101,0x50001040024030211,0x500010c000702021d,0x13000a051503021606]) else (readWords [0x2cc12600000214,0x4071016c400ec00681,0x484271102c125f828a,0x82e68e054206c01580,0xe3a250c312c27a8211,0x88c00000000d83ac1,0x91dd0292ca4187e6c6,0x9985c32cc292972599,0x389ef19c5c61e20000,0x80f8c2a9846642eb00,0xa8fb023610f4486e,0x827fc222000081f7d1,0xbc1e7f8681ca020000,0xc2c1427840b881c699,0x80818b85ac41b3c1fb,0xf311e494219010d91,0x914083810411b18294,0xd04200000000183982,0x2100f5032640652d3c,0x55041f26404a0de492,0x23d98742ca000000c6,628680737280,0xa9441da76e4d0000,0x9986126c88975e6d00,0x80e8000081ee0000,10419394,0x814209480c41190000,0x6437426bef30000000,0xc2d482570000,4773882456178724,0xec1e7b42cba1e581cf,0xc171c1f16e9400,0xc192c25c8225c18d,834991049728,0x54830b000001490000,0x830449b0c2834d2840,0x72405602d96d45e1d9,0x2d4d002741258323d5,0x50073418f01c3c311,0xc1fe80e202628168e1,0xba662000082e55a81,0x40ee0000c03dca0102,0x318d3bc1b8dd8dd2c2,0xe982169ecb923901,0xd622c28151000042aa,0x4075294c02f0c60a00,0xc19f01f90725c2d6,0x82aec0db9f0e82b8c2,0x5b01c7813dd30f41e5,0xc1ed91a9c02a00,0x91395b08123c609,0x4a9f00000000000000,0x10000010cdc1cc0000,0x8cfc000005ae113b59,0x28c0ecc1415ac28153,0x90f626f300da48fc91,0x9d0000000080cc0189,0x7050000016f10c0ed,0x339e7dc20a00000000,0x920901c0000000,0x9270000429bca26,0x401385c081ca50c700,2193031168,0x40410000000000,0x51eb00002ac282ac,0x303000082720000c0,0x340000c23400008ae3,0xc04702730242000000,0xd38917011852c8acf3,0x9ec6dec98170523a51,0xb4030640fc83070000,0xc1b041900000000042,0xd7c85f0000429c9988,8433730,0x4b0000024dda7a0000,0x809fc0ddc30800,0x4a9c4202031452c4,0x81f0028b80b7e2a000,0xc0794208006cd16e,0x9b05c1360000809201,0xd5000029455e62e6c2,0x6d2f41b6531712,0x810000dd7b0000df12,8356563819430029,0x1c1ec8c10f1f08419c,0x80e400008059000000,0x9a4033000000000000,0x5ef60000814fdd7a81,0x3f82ea832702f30a85,0x5ef00000954bc30dc4,0xe2407e828541a351a8,0x82e48036c061000000,3215876161536,0xe669c17b9da10000c0,0x9b021fc91bc032c188,0x8243083c030c02a300,0x8195416ad2c5c1fc,0xd6a0a665032e491000,0x401f6dfa099201da,0x2f2e4109000000,0xc2569d1a422d82b1,0xc12d41210000021b00,0x4181c30e00004094,0x491a0137c1abc082d2,0x2251a00a4a0254c0b4,0x27b021744d640f6c9,0x1ce85000b24d92dda9,0x8028c060c302d0bec2,0x8caebbc11d624a82a0,0x2d34008b0000032002,0x9e81650159c15f42a8,0x1b27c2b4c1d7844b41,0x124062eaa5c2478317,0x5c35018c28ed6affc1])) else (if j<3 then (readWords [71270725682593,0xe2a148ea0000810100,0x23000041d8000001ce,0x10000000000c32100,0xa6810000431d0000,0x82be020f5063a47000,0x51991e08c26e0a6a,0x40f342a681e340b500,0x5f0265dcff41a7454b,0x41e4c25f0228807088,0x1002ed4296c8148e48,0x10643316d9bc14b43,0x32889080fa80660134,0x411c0244c8ecc27c44,0xe002e7de7e80f282b3,0xda7958cec83bc00a4c,0xf7c0b152bb415bdacc,826912898944,0x3a11ae000000000000,0x59e2000066f0c2,0xdd000011f9000002d8,0x45000000fd80dfc0,0x1d80e700009ec2dc31,0x5d22d4fbe9b5c1b700,0x80cb99e50000014a,0x88542904919d9,0xdc02ff40bf02370226,0x80968003ddc681db01,0xa400000124403f0000,0x402540bc0329400900,1664303300608,0xc0c180fb0000000000,0x10c80000c17e0000,0x644fc0c081e8992fc0,0x6d00008019c1ef0000,0x81a201970000c0cd48,0x12d50681df81bd513c,0x829a817901b5401b48,0x6d00001d1800009d1c,0x8115008000000000c8,0x3700000dfa822e82c7,0xd19bd1a501c2000053,0x15000086e581f2819e,0x49b5e951000043,0x9000c00005eca0000,0xc5c780cae94d11,0x760000812a80a5820b,0x832b8002c2230000c0,0x26c92919d81e6300e6,0x1d7cc1f8c879211700,0x8101ecc88942339114,0xed2d01a80461c21e42,0x3e8064c20500001dcc,0x8313402f000042c512,0xf089440088800d0000,0xa902022bc21cdae582,0x1000004284000099a1,0x21582990000000000,966367641600,0x81aa00000000000040,0xf9cd3c00000030c2f5,0xcd8bc039416b00002e,0x911afe009e190b5de3,0x914e81017c82c242,0xcf00008c3b02480097,0xc451521d431a827082,0x4116bc16411be8220,0x422c804349909ef952,0x36c1eb828704e44259,0x80c545ca0000422ac0,0xf1e6500000000c255,0xddf8451f84679d88ca,0x81464f807a02cc8537,0x2dc5681c32ac2f11d,0xc300ea0000402b0000,281857228895,0x700001231423d91b3,0xe1dd80c4420c000082,0x290000e138c1829196,0xc2ce4663c2bc000001,0xc400006e8dd319d226,0x5036c218030f8aa681,0x8c1408156d3098142,0xa66dd2bf01e2c0a882,0xb58166c1174150c1ae,0x1d51c139051b1dfe42,0x4a457902951d1b0000,0x413180d980d749,0xe400f1828fc5c2c10a,0x4103893cc94a815e40,0x85521e01d98d29806f,0x4816432d80c745,0xccc8844069c264c102,0x2bb41d0104dc23800,0x2fb1ec1c90848e9,874122172763264,0x8a425a614500004638,0xc68300460000c17500,0x19900008162e186,0x4004487c000042,0x910000000040530c02,0xc1f6e6cb40a90d8f11,0xb90000c80ac5099f11,0x472a817dc07712c602,0x60c02980b940930057,0xc80f4a4bc11e01fa59,0x89c5864938e663c80b,0x4130c15a422f00cfc0,0x8c0000c03cc196518c,0xc04c827e40abc02442,0x768a5596c2c2770000,0x29f1aa046c240bdc1,0x2700000000420351c0,0x2a240fe8811c08f89]) else (readWords [4962098924894720,0x82ab9a1be29f0169,0x621b4145428602d200,0x821200a4d856,0xc0ba12630000000000,0xbe426ac32f00009174,0x81f401cb42af806a00,1123811328,0xe03901dc22e212e902,0xad40dc561b105f86e0,0xee930000c114000088,0x1d025d41e181fd01bb,0x81f3000040ad59d782,0x9740c2d2f110ec46cd,0x8ec205f30000c52800,34060801557129,0x1130000020d516c91,0xba5e0700004310d1f8,0xd8540809523880d000,0xc15d00000000e666,0xee909cd240a6004800,0x59834178006302a4,0x8058c04dc2c8d18311,0x925224000048399325,0xddc94319c1579da3de,0x814044018ed30ac049,0x23b407dde7c000099,0x2742d0c30a0000c06b,0xd2bd417a92c0000042,0x5e00000000408d8185,0x823f00005cd482,0x40e990c07fc1b9c0ac,0x81e0df1005fa000040,0xd541c541bed97e0000,0x8817c2ba891d040600,0x9c8818e1e681984050,0x4055880e80a3819ba2,0x814227016d0000aa26,0x11fa00004279aa4a41,0x6e0000000024ff0000,0x80e5c252000090f38d,0xb045ad624906cc41d2,0x158000002c4419300,0x8095000010370000,0x1ec20029b685c8d1,0x9e823542bfa1845262,0x493a00000000c12bed,0x4cdef28250c2821d25,0x404b5ef348f7025841,0x775ec7051742a7451e,0x813b813802468239c1,0x1b1233e04c10f082a5,0x92b866ee51a6e8f10,0x495cdbc1b1d22dc021,0xd98450f225a1419482,0x75c2f982e900748110,0xc12990c30000c06702,0xe381554120c0990000,0x49490084c91f421a41,0xe7c12cdde940c94d8d,0x82e84078d84d402083,0x229e66024151c54174,0x1e2ec0ff82d1d9d500,0x6e00002a8100128184,0x83300000926aed2ec5,0x2095ad014de6fcd2fc,0x4c610f25807c00a292,0x30000081c182b00a63,0x40d681cd40a141f541,0xba0000d1ab0000c207,5124749739050240,0x2d30000ae880000,0x8328d86082f71eef00,3229286400,0xc28d000042bdc1,0xd1864800005da80000,0x80aac02c9cdcdee480,0x101d4c10bc1ea0000,0x4947805c000086,0xa012f7000081612dbe,0x83248042887300ef80,0x400000428e904f192c,0x4e005dc163425100,0x8702c0515c34,0x413c455a8305001700])))
def gD (j : Nat) : Nat := (if j<1 then (readWords [0x99ff8fe7880a0e,0x18eec0cbbe66039,0x45800007e0761dd418,0x851602fac46c0a44f,0x8e2d41b00a483df013,0xc0af006010662c3e1f,0x5a5adc83308350ff9f,0xb1f8d1000804bea0c,0xe0e7e965500318662b,0x3feffe92f848000400,0x4badc007bff2b49001,0x8c51165e1ffe78810,0x54a5d7ff1cdf102095,0xcb80000392ada6fa91,0xbc82e3a85d04e2,0x400f00b0c2007190c4,0x805fa49a2332060512,0x73c12905ef828ac5,0x6787c001b824009295,0xd200ea1b9000000000,0xbfc00001bfcf3d7b,0xc035b9ffffe0000000,0x5e1557d71a0060baa,0x96800000000005fe00,0xdfe79ebde01ad80,131857279,0xc09be1bbc06a330188,0x7aff5a413aa8018218,0x1f5bc0004e06d602c2,0xe6fc00d5377af1541e,0x980d4400beb11b0291,0x3e38b506c02933e38b,0x11b1a91045f04f5b40,0xb10536d91f0ca7cc0a,0xa980a51b1be194f981,0x553014a36027f3506f,0x64d602936cefff8f48,0x562012a358f5fe00,0xe16604a8960001f002,0xf846b5b40b104d5388,0x17c33f00fde620122b,0x6463d241140243691f,0xf98016604a894bfc01,0xc2cc09512a54cbf97d,0x2a0a094017036840b2,0x314912c998a52d0588,0x978ff26a4b8b987052,0xc80555a9503aac4150,0x5255cb5841a874c884,0xd01aaf5423d549abc1,0x6101c86a0a5a6a8939,0xa8b410a5c608ca0ea2,0x785a8ac20b17211c51,0x86110a20c288181081,0x7c1685e05d0f93f1fc,0x981982e0241e81680,0xb9f33de610f29dc3e8,0x78180384c09312425,0x449c92acf9391ec634,0x8d05886104c1a580a2,0x1190610202cc6c06c1,0x522703e01f0be21839,0xbe0fa1885f8a80962,0x345a01a14613020c4c,0x7e144550d41a02523,0xe08e8c696a05c06101,0x3c1b890015016070d,0x98fb21a392bd50a99d,0x4e85b0620e83180000,0x81ec10a894fc940370,0x230c10621f82203c11,0xe3241c105026360b24,0xf49ae312460cc13814,0x7f83d05e2fa2282a2,0x303442282294d0d408,0xca22a2da3640507c1,0xe22949f86e0ec0d011,0x8436a2e40e1341aa4,0x540c82c0683b05704e,0x18a0fc409291e80187,0x4866080300901500a8,0x1142489919a2d81410,0x13a1444b00e0100e0,0x2d00602005019002b9,0xf587a75d14a7713279,0x44c7ee36f15b888438,0x61230628143f19eecf,0x1974f3891b34d6167d,0x31dd858bf65d2ad4d6,0x4aaf155029654069b8,0x4ada42d19688c425a0,0x10f7a7773969b04c84,0x5bc29e937094444c1f,0x90ed470e3531918b5c,0x5182410fb06a42ce10,0x105881d80760009663,0xcb2fe584f2b9f95c7c,0xae1e542f2a0f9646cb,0x36491b2cc496524b2,0x7259192c2496064b01,0x257492b9c95c24aa72,0x54392a0c94c64a6124,0x989249c964dcb24e58,0x372c139601caa4e550,0x7299394c1ca40e5815,0x2c09954ccb0425520a,0xcbf6597b2c9d963eea,0xe56622b2921709098,0x4564dab24e1206ac8a,0x5660ab2655912ac985,0x6480b2c819704ca036,0x4c23243ffffefdfefe,0xffdfbbef7bedfd7f58,0x1404c1204403008010]) else (readWords [155618,0x67259934a6b1ccffb,0x7406a1e14a4f13bfff,0xff9ff85c09f851030b,0x2684d0060b0726ba3,0x7ffffc2fbf9c6df106,0x850640b0b901f81125,0xd004fffffa81fe04c2,0xcc7da27100b9c86f8d,0x6574003ff64f4a8002,0x70048252a141005d05,0xe4f43ffffc4ffc2e04,0xfe0a2068989a134018,0x2c13f2f8077fc0be9f,0x48400a0926e00060,0x822cf2003b043cd20,0x7231120f800066015b,0xd520722f1a0000000,0x1bf819fcca2425f35f,0xe1423eef5313544018,0xe0b7a8c5e16bfc034,0x72f5cb20b170cda37f,0xcfc21a1242880301c0,0xf54b7cbb71810137a,0x401a8b4ffffff60cd0,0x40010000436a7fff1f,0x6d01241398a0001821,0x8014750ffff8000064,0x1a50028151b60039d,0x2bfc33e70094ab0,0x48205212602008d79c,0x7c02c541810438037f,0xfffe4411300060860c,0x27000efff6f4e04120,0x4c02680006008018ee,0xeff1c8da185c800822]))
def gJ (j : Nat) : Nat := (if j<2 then (if j<1 then (readWords [0x8ae000001c400,0x5168000000000,13,0x8ea0001041a14ad94b,0xa2f9110b467000184a,0xc0000000d05054a506,0xa80fa000180fc00020,0x4c49b7085c00042fcc,0x1fe00030ae80000000,5835696509719,0xf16b00000001833e0a,0x8000012a000000000,487752,0x8e4000000020740000,3129415,0x800070e60000013800,103691583488,42464,0x11186b3380000000,0,775,0xe80000001525c00000,0,0x184b400000008150,640902554162,13979942,0x300000000000000000,14032044032,0x857d039c2b444c4,6658273055515,0xc05680000000028000,0x8163817000000,4359192896,0x1022400061240000,18243584,0,461440,0x81fc232757300000,11774,91725658035585024,0x6099c0cda2c874,0xb80000001335400000,0,0x95730720000,6987,0xf1868000e9f59a5201,0x48000401c040400000,424437275426821,0x11c000000000000000,0x810000000000000000,72057707418353664,1349824,0x46d26600000006f700,4252,0x242d4f40c804000,0x30a00000ca36000000,0x985f051c00000,0,0x104c800000000001,0x3300000000c1105be,0x8000692a0000000000,0x82ac000000040,0x8a0000000000000000,1229848576,0,0,70044876800,0x82d400000000,0x10600000606c0000,0x20218148000005f,11699200,0,78643200,0xa19c00060d20000,0xb00000000015f,832116359168,0,425545360081808,386564538718,115400704,309533368945668,0xd00000001005400000,0,16529,0x844c45680000001056,0xc0000000000002c120,0xd914b01900419a3d00,0x8006025f21f4f714,0xd68000005480000000,0x328880000000000,0x26310000bcdc00,50390368260,0x9124f8b0a00900000,2732689719297,0x9c0d0550000000012c,0x713a8959000034c745,0xd80000000000000000,62844325855232,18116716726490,0x908400040900460000,0x303b00000000bd1000,0xd1a112a800000,0x2d2880f4000600d3,0x400412246035106000,0x22733020201321274,0x4513207000000507,0x2a301113130020210b,0x81043010000000c000,0x16100010064028024,0x520010120056011014,0x402310003150401010,0x300103010012031250,0x1300100100201006,0x220001001100210]) else (readWords [9007408298852433,0x6a5be3699000000008,0xa3c000000000000000,0x2a000000000002022,0xc2e30000048400060a,0x1000024a007c000091,0x74000000000009d480,0,0,0x89900000000000000,0xb9744310000c2,0xc2000000000004d480,0x233766b200009414,0x840000d9d18966468,0x80f600000003414800,0x5eb00002479800000,856030163501056,0x6c80000001807b,0x419600c000083012a9,0xe09b00000000000000,0xad300000000000000,2963275778,0x56c000000000000000,0x60cd00000000000,520,0x542d000016b80000c8,0xdc000000000d600011,0x2c000217b00008293,0x9a00000000084dc000,773027004416,2109314,0x2a29d70b5000000000,0x23498000022c0003,0x65e40056ae20d2c000,37957632,64212822917120,0x84da22d800002ed0,0x4c0000000c2960000,0xea00000000000,4622388423557120,0xe1e40000000411400,0xa260000014600000,0x601726820000,12303,0xc07d00000000000217,0xac8de0020000093940,0x7c0000000605000018,0x21d03cc11f000184cc,180388626432,0x9382ac000000,81822482520,0x64000000e000000012,0xb805fe92300000001,0xb15c14d00ac0000000,0x4254000000016e,0xc0001b1b8000289700,21798846464,0x102ee6f8c9e60000,0x609800000000000,0x493a00012ce4000626,0x7000000030aba1281c,0xa80000007800000000,2,0x495800000000000000,0,0,28012707840,0,0x415381f72254000,1901462554293,0x600010178000000000,0x829c0000000c2920,80304,498618370,0x42c6000000040a,0x200000001193000000,0x1cd10000245dd2ae0,0x207be03000012b08,0x759800000000000171,1289362604032,0xc25e840a0988e7b81,0x580515a8c000059448,0x3c800020e0000110fc,0x616742460000000,0xbd00000000000000,0x594680a8000000000,727711744,33156,19327357095,0x8000000184b8000000,0xd26f88b4000000000,298052,0xbaa086e03400000000,0x62000000000001235,40464384,0,265792,44800803944874,0x304790221a51055e,0x407501fc000208,0x4821c00000000000a8,0xf0a885185000000000,7599824414703616,2199,0xe13000010412048cf4,0x20000d1b0000610782,0x2e45fa02b800000018,0x298000610f00000000,8577,0x80000000011c06e2d3,0x500000000465800000,0x1142eb39767100000,2854823328,13390])) else (if j<3 then (readWords [17666408449,0x84b66e000000000000,0,0x829c839e169800042d,0xa000201ac0b6000182,0x380000000c61732da4,0x693498000000000000,0x7c81ae00000000000,0xddda00000000000000,9210059150065664,0,2,0xc7000000000000000,0x92c684600000000c1d,0xc02c900500000000a0,0x440000000000000032,0x3c0000000000000000,19568,0x1ad2c0004152416,0xe80880000000add200,0x20380000c05c00000,0xccca00000000,0xdb000000000000000,43433984,4555826429689856,0x1221e0ce000181a81,0x1944fe00018129a89a,0x64de30000041d0000,413696,9047552,34579939382,0x390000000000000948,26585847562240,2199023255552,0x180760ba0000000000,752135071866756,0x3f8000000000000002,0x86881f800000006082,98304,4567921057595392,0x1068e0bba1ca05700,0xae2a00000000,8952,34709504,524346,0x800000000000000000,0x60d381dea5240000,0,2247140537000,0xe0000000703c000000,58314987568,0x49b2b3000000010528,0x88bc000229c8000,88886732166006292,0xa00012364924000102,0x2c00000005d200327a,0xbf8000028400000004,0xcfe20ea00030bbe894,107429888,0x2779804180b600,579567856131594,0x94095d5277c1df09a8,0xb3000000000000000,0x83980000000000,202056976896,0x201d8000000000037,0x6be22ed10c00000198,26417541316608,43276316,0x70278000000044d800,0x32318000894800000,7828212384,0x51c0b000000000000,0x98a9cbcc0000000000,0x3634f6b9000081,0x4c0006962000183b22,0x400000000000244de,0xeaf00010059089530f,0x860400000000000000,54839086265344,734003200,47141561040896,4037818753167,73574920184967168,8472064,0x60eb82d680ad0,0xb60000d55200000006,0x6b000000010aaa0d0,3317325365248,0,74766790688826,0x5ce493013a13d485ac,0x67000000000000000,0x94ce00000000000000,0,25,0x72a746000002e6b190,0xa3da0008000,0x20a00010430000000,6207843913054212,0x880220000000000037,0x4aa26eddf200000000,0x444e00024b58000,2225195712512,0x5cc494c16e000000,0x24b4f45d000000026,0x49202540a424f00000,0x29f81b050a59708000,0x4f04e24188000000,0,727086652194816,0x2960c0b200022852,0x8330000db7c0000000,0x42c800000000000827]) else (readWords [22626672790,0x7a00d0000000000004,0x8b4049aa4dc81b266f,0x832a755e4975a6891a,0x603de0f30000000205,0xd0000007800000006b,0x984ca937c08d8000c,0x23a000172dc12082c4,0x85110bc0000d135004,0x146a00009caa0ad712,0xe422f0218000000000,0xb4000000060200,0x904000000000000,0x18bf80000000000,0x1b8900000000000270,0xc80000000000000000,0x806400000000,53015490789530,0x202100000001842,0xc00010e40000c96c00,0x32c11a000109d25,0x60000000000000000,0xb1f42724ae0,0x20848000000083d,0x449700000a5013ec1a,0x6f63a0000000000000,0x80000103b40000000c,0x27a000000000000000,0x9029a3b80000000000,0x309a00000000000000,24868028416,5876,0x552844400000000000,0x33830000000005c,0x800000000000000342,0x68000c94c0001777ad,0x7c0000000109606728,0x15c5bac00000009a96,2250831301127,0xa443d02e0001a50101,0x8895100004a5477000,0x42fa000307800004,0x138000000000000001,0x85c00000000418a000,0x413f0000000000,40656777018496,0x119b23c7274a8a98,0x528000000000000000,0x67c402880dc00b,0x40000000c85785e400,0x166f82cb849400000,0x1dc48cb400000000,17911155261441,0xc38f200a56d48e2809,0x811e00000000a2e400,14,0xe4000085680004f6d0,0x1325000000000000,67756032,0,35029779328,0x41c5a33c00000000,0,6155,184046059520,64,0x94ae391f800036770,0x1a0c00000000c1ca,0x206582230000000,17146880,80341893128,0xf70000000000000004,0x1a92d3400005180000,73799220523646976,121,0x400000001838769c00,0,35869096083456,75338536745435136,901406262073,0x300000000253f49e81,0x3c286000144680000,0x837800000000000,201465856,0x105e0d80000184ec00])))
def gE (j : Nat) : Nat := (readWords [0x7ffffe000017e0,0x10944e400000002fff,0x97991d6494e800fff0,0xbf2a0c06404fe00,0xb950499fc055100a3,0x8000fe26242400007f,0xf2f09a1617fe00190c,0x5617fe06002054911,0x7a2510a3384a4e9fc3,0x61524e0fa3e03e2f90,0xc3917e5f1502d8f646,0xc410d9f27b984791dc,0xc0120300205020040,0x1a01860138764508e2,0x88c86a0501f82c0f02,0x61d0c613066170243d,0x28168d6760620381e,0xd03a0209607042110,0xa200a831016000040,0x60900a823d1bacb1ee,0xca4d18860005916050,0x130481100c020043ff])
def gK (j : Nat) : Nat := (readWords [0xd078000000000,0x10b16ef035b8d00060,0xd400000041c0000000,1051136,0,9793122970,0xf1074e2801b30d8928,0x173a92a812c0b102,0x511f000a24021bab10,0x120000650000000000,0x101600000000220180,0x88e6a840008155ca,0x8d000081c24b80024,0x100000000002054000,0x447800000000000000,0,0xc3d456800107600000,0x60f40000000000002,0x4200048c228720400,0x289800010be8a0,0,977105059840,845258992648192,0xc0280000000,0x60d2023820000,20447232,4947802324992,2713766806,0x88000000c19c474108,0x8018000a3000040,0x200000000020000248,0xa2900060fc00000,0x1f00000000000004,0x1c000000e990cac65,0xc00081180880000004,0xc8000001905490800,0x3750000000000145c0,576144092954624,0x536000516e8a80,0x98003078000,0xc8d000203a00000000,0x2456000000000063b,0x836000000000000000,4184,0x914000000000,0,53095855104,0xbb900000000000000,0x20c5114000000000,0,0x4830000000000000,163208757248,0x5080ce4000000,0x69160ca1363b701700,0x102f0390006453460,5770238655307877,402490243678209,0x50000000206c00001,0x44076040b30037c07c,0x2262000000000000,0x1bab88000af05a0000,0x2cdc000000000000,5101735070864864,0x105800208308e000,263680,35600581263360,0x4c380000006c860,0xbc24800008d8003534,17819883343040,0xb000000000091a8000,0,6,0x2e000088d000244800,0x181f00c60088050800,0x11400010051002008,0x1c0084222500080020])
def gF (j : Nat) : Nat := 0x403103b437ff
def gL (j : Nat) : Nat := (readWords [48,0x400222000000000000,0x42000000000000067,0x107c080000000000,8673820672,0x8cc00000000000,0x951970000095f0600,0x231000000000000000,0x5c40000000000000d0,5200,35634806784,0x61c000000000,0,1267015352320,4630511616,57868288,85487029059721,0x400000000000000000,0,0x9000000000000,0x11000000000000000,0,803840,154618822656,0xedc00000008,0x5c0000000000000000,0x293000000000054,0,0xd1c000000000318000,0x5dc0000000000000,0,0,0,0,0,20938025344,0,0,0x3a70000000000000,0,7171,148992,0,0xc0c000000000000000,0,23,0x400000000000012100,0x253000000000000000,0x1860000000000000,0x35100000000000,51606716416,208305913856,0,0,0,0x9800000000000,0,870,1024])
def tX : Nat → Packing
  | 9 => (7,6,9,393221,51,6,4096,nH)
  | 10 => (182,5,9,5963854,119,11,4144,gA)
  | 11 => (820,4,9,5898424,120,14,4465,gB)
  | 12 => (386,3,9,1769521,86,15,4664,gC)
  | 13 => (66,2,9,655368,67,13,4360,gD)
  | 14 => (9,1,9,65537,0,9,4180,gE)
  | 15 => (1,0,9,65537,0,0,4099,gF)
  | _ => emptyPacking
def moIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupShort 3 61 1 8 3 3 gG
  | 11 => lookupShort 65 977 3 14 8 4 gH
  | 12 => lookupShort 353 1741 8 16 10 4 gI
  | 13 => lookupShort 199 1993 4 15 9 4 gJ
  | 14 => lookupShort 40 409 5 13 7 4 gK
  | 15 => lookupShort 12 431 1 10 4 4 gL
  | _ => fun _ => none
def mo : Forest := ⟨1535,15,fun i => moY[i]?.getD (0,0),moC,moA,tX,moIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem w0 : graphValid mo (boundsBefore pri) = true := by
  simp only [graphValid, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,pieces_all (d:=6) ?_⟩,pieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nL : CutRow mo 9 0 7 :=
  (@joinRow mo 9 0 6 1
  (checkedPanel 0xce6632990c662)
  (checkedCut 0x31401265))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nB : CutRow mo 10 0 182 :=
  (@joinRow mo 10 0 87 95 (@joinRow mo 10 0 72 15 (@joinRow mo 10 0 5 67
  (checkedRow (checkedCells 9 0 0))
  (checkedPanel (readWords [35983495,0x43215088321a090242,0x401fcfc000d8a43440,0x1f400003e1ec3219,0xc9e8f2193c1dc5000,0x910408003b0000075,0x200fc3074001cc2412,0x3909c4e710c1c0de6e,0x369b0303f359a8d268]))) (@joinRow mo 10 72 1 14
  (checkedRow (by decide +kernel)) (@joinRow mo 10 73 13 1
  (checkedPanel (readWords [1943625080874,0x47a38884446a31168a]))
  (checkedRow (by decide +kernel))))) (@joinRow mo 10 87 52 43 (@joinRow mo 10 87 11 41
  (checkedPanel (readWords [39397916,0x4a24c381c490ac562b])) (@joinRow mo 10 98 2 39
  (checkedRow (by decide +kernel))
  (checkedPanel (readWords [0x2bd5cad0012158ab,0xf07404aa548a15047,0x53a9804285281082a4,0x2328d44a15027d3c9d,0x4e26c08044d2653097])))) (@joinRow mo 10 139 39 4
  (checkedCut (readWords [6661424,0x108746a23284b68383,0x65ab401003ba047365,0x6b4010a36b48723746,0x723265613010093655,0x73565a30707868a291,0x9065573314312767b,0x4b8964654b3196891b,0x5ba3654131968786a2,0x108786a2218786a221,0x8786a221929b076156,0x5630708786a2806560,0x309665653096656530,0x96656530967868a291,0x8786a2218786a29114,0xa19010533412715334,0x12715334127113ba04,0x725334127126b43076])) (@joinRow mo 10 178 1 3
  (checkedRow (by decide +kernel))
  (checkedCut (readWords [7780721,0x21426b234314a59010]))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nC : CutRow mo 11 0 820 :=
  (@joinRow mo 11 0 504 316 (@joinRow mo 11 0 399 105 (@joinRow mo 11 0 112 287 (@joinRow mo 11 0 7 105
  (checkedRow (checkedCells 9 0 0)) (@joinRow mo 11 7 96 9
  (checkedRow (checkedCells 10 0 4))
  (checkedRow (checkedCells 10 0 0)))) (@joinRow mo 11 112 192 95 (@joinRow mo 11 112 96 96
  (checkedPanel (readWords [0x92f00402002ed7400,0x40004001300000,0x12d7200000080802,0x20117002010085ab7,0x168b40a05028140a0e,0x70381c0e0007c1c0e,0x160b0584a2504c0201,0x9820261309ad96ab4,0x40041001040201005,0x28140a0b058016649,0x24868000b59068361a,0x28140a05042c410b0]))
  (checkedPanel (readWords [3591,0x66921981e0f32c3c52,0x6507c0c50033240609,0x488812c8148bc0c09,0x48258e216308464c5,0x27800420310b10a215,0x100542ac3610c02a20,0xa880a2c118b006031,0x188c0a02f1793c280c,0x270b800000000000bf,0x5f13402000312c24bd]))) (@joinRow mo 11 304 94 1
  (checkedPanel (readWords [0xb2451a8ddc0df,0x1bb78b0dd6e1606837,0x21b6c64571b0306c0c,0x1a95c6c0c04b688c35,0x6c959b0221a154a8d7,0x2a359aa5329b51a6d2,0x68b400ccf6708c0c02,0x10000000000000000,0x58003600118000000,0x8000201008043600,0x11804660003000000b,0x58001008040601000]))
  (checkedRow (by decide +kernel))))) (@joinRow mo 11 399 23 82 (@joinRow mo 11 399 2 21 (@joinRow mo 11 399 1 1
  (checkedPanel 225)
  (checkedRow (by decide +kernel))) (@joinRow mo 11 401 20 1
  (checkedPanel (readWords [31333555744,0x789c1e0f1739dcce5,0x7b91c60f06030b2e2]))
  (checkedRow (by decide +kernel)))) (@joinRow mo 11 422 13 69 (@joinRow mo 11 422 10 3
  (checkedPanel (readWords [26674,0x76bb070071c3ac70ea]))
  (checkedRow (by decide +kernel))) (@joinRow mo 11 435 68 1
  (checkedPanel (readWords [537398274,0x1412070203170b901,0x8004400ff000000803,0x23f9fa5b0b3f1f6fa,0x7c82412f87b8582cf6,0xb3d42c0a1d3d0183a,0xa3cde4147883c7409,0x48a8545a2b3c1de39,0xa1385c090a03018ee]))
  (checkedRow (by decide +kernel)))))) (@joinRow mo 11 504 195 121 (@joinRow mo 11 504 89 106 (@joinRow mo 11 504 5 84
  (checkedPanel 275146343483) (@joinRow mo 11 509 1 83
  (checkedRow (by decide +kernel))
  (checkedPanel (readWords [76432673,0x9047e3c000002ca41f,0x8e81e38000f8000417,0x8d85c463b0b80a341d,0x1dc64be5f8c05c0000,0x80517030f40200,0xb800aa428b08a2b14,0x180cbc2489c4a223d,0xe8f03a3c1e168bb10,0x2ec3e1d0d238e4730c,0x85c2a130883c1a0a04])))) (@joinRow mo 11 593 3 103 (@joinRow mo 11 593 1 2
  (checkedRow (by decide +kernel))
  (checkedPanel 150308)) (@joinRow mo 11 596 96 7
  (checkedCut (readWords [0x8796a2328746,0xa2328746a23214a190,0x103183123214ab9010,0x65ab401076b8612165,0xab301076b8612165a1,0x401070b9a12165ab30,0x1065ab301065ab3010,0x65ab301065ab301070,0xb8a12170b8a1212618,0x3121754b297565ab30,0x1076b8612165a53010,0x65ab301065ab301065,0xab3010658b301065a1,0x301070b8a19170b8a1,0x9170b8a19170b8a191,0x70b8a191133912a213,0x3912a2133912a270b8,0xa19135ab043070b8a1,0x9170b8a19165ab3010,0x765861217658612176,0x58612165ab301065ab,0x301065ab301070b8a1,0x2170b8a121a1b68661,0xa1b6865076b8612176,0x5861213146129270b8,0xa12170b8a12190a055,0x403bb618978796a221,0x8786a2218796a22187,0x96a2218796a2218796,0xa2218796a2218796a2,0x218796a2218796a221,0xa1b68650531a049376,0x58612153ba0493a1b6,0x866153ba04938796a2,0x32531a0493a1b68650,0x76b8612153ba0493a1,0xb6866103ba049353ba,0x49313391292133912,0x9214ab901014ab9010,0x314612323146123231,0x46123214ab901014ab,0x901014ab9010426b23,0x4335ab0440426b2343]))
  (checkedCut (readWords [135,0x86a2218796a2328796,0xa2328796a2328796a2,0x328796a2328796a232]))))) (@joinRow mo 11 699 72 49 (@joinRow mo 11 699 40 32 (@joinRow mo 11 699 1 39
  (checkedRow (by decide +kernel))
  (checkedCut (readWords [11959050,0x8656b6308070b9a121,0x560a3080560a308056,0xa30808786a2218786,0xa2218786a2218786a2,0x21093a55848786a221,0x8786a2218786a22187,0x86a2218786a221093a,0x55848786a2218786a2,0x218786a221a1b78650,0x8786a221754b296487,0x86a2a2a1b78651a1b7,0x8661b67b0a75a1b786,0x518786a2a226193181,0x261931812619318178,0x68a2a226193181b67b,0xa75261931818786a2,0x21b67b0a75a26a2872]))) (@joinRow mo 11 739 1 31
  (checkedRow (by decide +kernel))
  (checkedCut (readWords [0x754b2964265431,0x21b4a49550b4a49550,0xb4a495508796a221a1,0xb78650a1b78650a1b7,0x865046ba7080a1b796,0x50a1b78651b67b0a86,0xb67b0a86a1b7866187,0x46a23242642343b67b,0xa8665a14010b67b0a,0x86b4a495408796a232,0x319612328796a23287,0x96a232314612323146,0x1232656b3010656130,0x10b464b550b67b0a86])))) (@joinRow mo 11 771 4 45 (@joinRow mo 11 771 1 3
  (checkedRow (by decide +kernel))
  (checkedCut (readWords [10598022,0x61929b07728796a232]))) (@joinRow mo 11 775 1 44
  (checkedRow (by decide +kernel))
  (checkedCut (readWords [484150682004,0x6475503746723294a4,0x755076b9712176b971,0x2170b8a12165ab3010,0x8785b23270b8a12131,0x85123265a530107058,0xa12170b9a12114ab90,0x1065a5301026593121,0x261931216585301065,0x853010261931212619,0x31218796a2328796a2,0x328796a2328796a232,0x65a0301014a0901065,0xa030102654312165ab,0x401065a5401065a540,0x10a1b6866165a54010,0x65ab401065a5401065,0xab40108796a2326561,0x30108796a23270b9a1,0x2170b9a12114a59010])))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nD : CutRow mo 12 0 386 :=
  (@joinRow mo 12 0 311 75 (@joinRow mo 12 0 265 46 (@joinRow mo 12 0 233 32 (@joinRow mo 12 0 62 171
  (checkedRow (checkedCells 10 0 3)) (@joinRow mo 12 62 96 75
  (checkedRow (checkedCells 11 0 4))
  (checkedRow (checkedCells 11 0 4)))) (@joinRow mo 12 233 10 22
  (checkedPanel (readWords [77,0x13004041f0f87d26])) (@joinRow mo 12 243 1 21
  (checkedRow (by decide +kernel))
  (checkedPanel (readWords [757393528321,0x30180c00000000207,0x3ca423280680c4527]))))) (@joinRow mo 12 265 31 15 (@joinRow mo 12 265 1 30
  (checkedRow (by decide +kernel)) (@joinRow mo 12 266 29 1
  (checkedPanel (readWords [20617194788352,0,68853957156,0x8040201148cc672a]))
  (checkedRow (by decide +kernel)))) (@joinRow mo 12 296 13 2
  (checkedPanel (readWords [688539720714,0x516c140a128284b2d])) (@joinRow mo 12 309 1 1
  (checkedRow (by decide +kernel))
  (checkedPanel 10))))) (@joinRow mo 12 311 25 50 (@joinRow mo 12 311 14 11 (@joinRow mo 12 311 1 13
  (checkedRow (by decide +kernel)) (@joinRow mo 12 312 6 7
  (checkedPanel 0x4a0a08040212f)
  (checkedRow (checkedCells 12 0 0)))) (@joinRow mo 12 325 6 5
  (checkedPanel 584087983513613) (@joinRow mo 12 331 1 4
  (checkedRow (by decide +kernel))
  (checkedPanel 4857161824)))) (@joinRow mo 12 336 9 41 (@joinRow mo 12 336 1 8
  (checkedRow (by decide +kernel)) (@joinRow mo 12 337 7 1
  (checkedPanel 0x402026130982026)
  (checkedRow (by decide +kernel)))) (@joinRow mo 12 345 22 19
  (checkedPanel (readWords [604801862998565,0x680c0603018340603,0x9a97806030180c1a03])) (@joinRow mo 12 367 1 18
  (checkedRow (by decide +kernel))
  (checkedPanel (readWords [49979,0x9d4e671370381c0e07,0x381c7b36038442211])))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nE : CutRow mo 13 0 66 :=
  (@joinRow mo 13 0 5 61
  (checkedRow (checkedCells 9 0 0)) (@joinRow mo 13 5 18 43
  (checkedRow (checkedCells 10 0 1))
  (checkedRow (checkedCells 11 0 3))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nF : CutRow mo 14 0 9 :=
  (checkedRow (checkedCells 10 0 0))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nG : CutRow mo 15 0 1 :=
  (checkedRow (by decide +kernel))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem tY : mixedTables mo 15 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty mo 0 0
  · exact mixedEmpty mo 1 0
  · exact mixedEmpty mo 2 0
  · exact mixedEmpty mo 3 0
  · exact mixedEmpty mo 4 0
  · exact mixedEmpty mo 5 0
  · exact mixedEmpty mo 6 0
  · exact mixedEmpty mo 7 0
  · exact mixedEmpty mo 8 0
  · exact nL
  · exact nB
  · exact nC
  · exact nD
  · exact nE
  · exact nF
  · exact nG
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem monoRoot : Impossible false graph 15 inputs.toFinset := by
  rw [show graph = targetOf mo by decide +kernel]
  exact mixedRoot (g:=mo) (top:=15) (i:=0) (before_sound pri nI) w0 tY (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_18007.NineInputs

namespace PEqualNP.Outside.L_meta_18007.NotBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
    (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def base (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [x 0 && x 2]

def inputs (k : Fin 12) (x : Fin 10 → Bool) : List Bool :=
  base x ++ [!(base x).getD k.val false]

end PEqualNP.Outside.L_meta_18007.NotBudget

namespace PEqualNP.Outside.L_meta_18007.Dependence

open PEqualNP.Outside.L_meta_18007.NotBudget (target)

private def neighbor (p q : Fin 10) : Fin 10 :=
  (![
    ![1,4,4,1,1,1,4,1,1,1],
    ![2,0,0,0,2,2,0,0,0,0],
    ![3,3,1,1,1,1,3,1,1,1],
    ![2,4,4,2,2,2,2,4,2,2],
    ![3,3,0,0,0,3,0,0,0,0],
    ![7,7,0,0,7,0,0,0,0,0],
    ![8,8,8,1,1,1,1,1,1,1],
    ![2,5,5,5,2,2,2,2,2,2],
    ![3,3,5,5,5,3,3,3,3,3],
    ![6,4,4,6,6,4,4,4,4,4]
  ] : Fin 10 → Fin 10 → Fin 10) p q

private def witness (p q : Fin 10) (b : Bool) : Fin 10 → Bool :=
  fun i => decide (i = neighbor p q ∨ (i = q ∧ b = true))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2500000 in
private theorem witness_valid (p : Fin 10) : ∀ q : Fin 10, p ≠ q → ∀ b : Bool,
    witness p q b p = false ∧ witness p q b q = b ∧
    target (witness p q b) = false ∧ target (Function.update (witness p q b) p true) = true := by
  fin_cases p <;> decide +kernel

theorem dependence_update (p q : Fin 10) (different : p ≠ q) (b : Bool) :
    ∃ x : Fin 10 → Bool, x p = false ∧ x q = b ∧
      target x = false ∧ target (Function.update x p true) = true :=
  ⟨witness p q b, witness_valid p q different b⟩

theorem dependence_at_value (p q : Fin 10) (different : p ≠ q) (b : Bool) :
    ∃ x y : Fin 10 → Bool, x p = false ∧ y p = true ∧ x q = b ∧ y q = b ∧
      (∀ i, i ≠ p → x i = y i) ∧ target x = false ∧ target y = true := by
  obtain ⟨x, hp, hq, hOff, hOn⟩ := dependence_update p q different b
  refine ⟨x,Function.update x p true,hp,Function.update_self _ _ _,hq,?_,?_,hOff,hOn⟩
  · exact (Function.update_of_ne different.symm true x).trans hq
  · intro i hi
    exact (Function.update_of_ne hi true x).symm

private def emptyRow : Fin 10 → Bool := fun _ => false
private def singletonRow (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = i)
private def edgeRow : Fin 10 → Bool := fun i => decide (i = 0 ∨ i = 1)

private theorem target_empty : target emptyRow = false := by decide +kernel
private theorem target_singleton : ∀ i : Fin 10, target (singletonRow i) = false := by
  decide +kernel

theorem target_not_constant (b : Bool) : ∃ x : Fin 10 → Bool, target x ≠ b := by
  cases b
  · exact ⟨edgeRow, by decide +kernel⟩
  · exact ⟨emptyRow, by decide +kernel⟩

theorem target_not_signed_primary (i : Fin 10) (negated : Bool) :
    ∃ x : Fin 10 → Bool, target x ≠ (if negated then !(x i) else x i) := by
  cases negated
  · refine ⟨singletonRow i,?_⟩
    change target (singletonRow i) ≠ singletonRow i i
    rw [target_singleton i]
    simp [singletonRow]
  · refine ⟨emptyRow,?_⟩
    change target emptyRow ≠ true
    simp [target_empty]

theorem target_not_signed_hint (negated : Bool) :
    ∃ x : Fin 10 → Bool, target x ≠ (if negated then !(x 0 && x 2) else x 0 && x 2) := by
  cases negated
  · exact ⟨edgeRow, by decide +kernel⟩
  · exact ⟨emptyRow, by decide +kernel⟩

end PEqualNP.Outside.L_meta_18007.Dependence

namespace PEqualNP.Outside.L_meta_18007.RawWires

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

private theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_getD_lt _ _ _ h

theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]; simp; omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · rw [if_pos hi, hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · rw [if_neg hi, List.getD_eq_default]; omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self, List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

theorem wires_gate_of_input_reads (C : Circuit) (x : List Bool) (j : ℕ)
    (hj : j < C.gates.length) (reads : ∀ t ∈ C.gates[j].inputs, t < x.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun t => x.getD t false) := by
  rw [wires_gate C x j hj]
  congr 1
  apply List.map_congr_left
  intro t ht
  have ht' := reads t ht
  rw [rd, if_pos (by omega), wires_input C x t ht']

private theorem wires_rel (C : Circuit) (a b : List Bool) (hl : a.length = b.length)
    (R : Bool → Bool → Prop) (keep : ℕ → Prop) (zero : R false false)
    (initial : ∀ i < a.length, keep i → R (a.getD i false) (b.getD i false))
    (compatible : ∀ g ∈ C.gates, ∀ f f' : ℕ → Bool,
      (∀ i ∈ g.inputs, R (f i) (f' i)) → R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map f')))
    (gate : ∀ j (hj : j < C.gates.length), keep (a.length + j) →
      R ((C.wires a).getD (a.length + j) false) ((C.wires b).getD (a.length + j) false) ∨
        ∀ t ∈ C.gates[j].inputs, t < a.length + j → keep t) :
    ∀ i, keep i → R ((C.wires a).getD i false) ((C.wires b).getD i false) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hi
      by_cases ai : i < a.length
      · rw [wires_input C a i ai, wires_input C b i (by omega)]
        exact initial i ai hi
      by_cases gi : i < a.length + C.gates.length
      · let j := i - a.length
        have hj : j < C.gates.length := by dsimp [j]; omega
        have index : a.length + j = i := by dsimp [j]; omega
        rw [← index]
        rcases gate j hj (by rwa [index]) with equal | inputs
        · exact equal
        have wb : (C.wires b).getD (a.length + j) false =
            C.gates[j].op.eval (C.gates[j].inputs.map fun t => rd C b (a.length + j) t) := by
          rw [hl, wires_gate C b j hj]
        rw [wires_gate C a j hj, wb]
        apply compatible C.gates[j] (List.getElem_mem hj)
        intro t ht
        unfold rd
        by_cases before : t < a.length + j
        · rw [if_pos before, if_pos before]
          exact ih t (by omega) (inputs t ht before)
        · rw [if_neg before, if_neg before]
          exact zero
      · rw [List.getD_eq_default _ _ (by rw [wires_length]; omega),
          List.getD_eq_default _ _ (by rw [wires_length]; omega)]
        exact zero

private theorem congr_gate (g : Gate) (f f' : ℕ → Bool)
    (h : ∀ i ∈ g.inputs, f i = f' i) : g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  congr 1
  exact List.map_congr_left h

theorem eval_eq_of_read_agreement (C : Circuit) (a b : List Bool) (hl : a.length = b.length)
    (output : a.length ≤ C.output)
    (gate : ∀ j (hj : j < C.gates.length),
      (C.wires a).getD (a.length + j) false = (C.wires b).getD (a.length + j) false ∨
        ∀ t ∈ C.gates[j].inputs, t < a.length → a.getD t false = b.getD t false) :
    C.eval a = C.eval b := by
  let keep := fun i => a.length ≤ i ∨ a.getD i false = b.getD i false
  apply wires_rel C a b hl Eq keep rfl _ (fun g _ => congr_gate g) _ C.output (Or.inl output)
  · intro i hi hk
    exact hk.resolve_left (by omega)
  · intro j hj _
    rcases gate j hj with same | h
    · exact Or.inl same
    · right
      intro t ht _
      by_cases small : t < a.length
      · exact Or.inr (h t ht small)
      · exact Or.inl (by omega)

theorem exists_consumer_of_eval_ne (C : Circuit) (a b : List Bool) (hl : a.length = b.length)
    (output : a.length ≤ C.output) (j : ℕ) (outOther : C.output ≠ a.length + j)
    (different : C.eval a ≠ C.eval b)
    (others : ∀ q (hq : q < C.gates.length), q ≠ j → ∀ t ∈ C.gates[q].inputs,
      t < a.length → a.getD t false = b.getD t false) :
    ∃ q, ∃ hq : q < C.gates.length, j < q ∧ a.length + j ∈ C.gates[q].inputs := by
  by_contra absent
  apply different
  let keep := fun i => i ≠ a.length + j ∧ (a.length ≤ i ∨ a.getD i false = b.getD i false)
  apply wires_rel C a b hl Eq keep rfl _ (fun g _ => congr_gate g) _ C.output
    ⟨outOther, Or.inl output⟩
  · intro i hi hk
    exact hk.2.resolve_left (by omega)
  · intro q hq hkeep
    have qOther : q ≠ j := by
      intro eq
      exact hkeep.1 (by rw [eq])
    right
    intro t ht before
    refine ⟨?_, ?_⟩
    · intro eq
      exact absent ⟨q, hq, by omega, eq ▸ ht⟩
    · by_cases small : t < a.length
      · exact Or.inr (others q hq qOther t ht small)
      · exact Or.inl (by omega)

private theorem eval_op_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f f' : ℕ → Bool) (h : ∀ i ∈ g.inputs, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with he | he
  · simp only [he, GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i hi (H (f i) ⟨i, hi, rfl⟩)
  · simp only [he, GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hi hx⟩

theorem eval_true_of_read_monotonicity (C : Circuit) (a b : List Bool) (hl : a.length = b.length)
    (output : a.length ≤ C.output)
    (ops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ordered : ∀ j (hj : j < C.gates.length), ∀ t ∈ C.gates[j].inputs,
      t < a.length → a.getD t false = true → b.getD t false = true) :
    C.eval a = true → C.eval b = true := by
  let keep := fun i => a.length ≤ i ∨ (a.getD i false = true → b.getD i false = true)
  apply wires_rel C a b hl (fun x y => x = true → y = true) keep (fun h => h) _
    (fun g hg => eval_op_mono g (ops g hg)) _ C.output (Or.inl output)
  · intro i hi hk
    exact hk.resolve_left (by omega)
  · intro j hj _
    right
    intro t ht _
    by_cases small : t < a.length
    · exact Or.inr (ordered j hj t ht small)
    · exact Or.inl (by omega)

end PEqualNP.Outside.L_meta_18007.RawWires

namespace PEqualNP.Outside.L_meta_18007.RawCofactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.NotBudget (target)
open PEqualNP.Outside.L_meta_18007.NineInputs
  (Wire Constant inv combine Available supply Reach inv_constant from_constant available_cons
    Row Sig bit observe graph inputs sample edge edge_table Lower lower_impossible graph_proper
    monoRoot input_list absentRow670 presentRow670 requiredInputs)

private def cyclePetersen : Fin 10 → Fin 10 := ![1,2,3,4,0,6,7,8,9,5]
private def twistPetersen : Fin 10 → Fin 10 := ![5,7,9,6,8,0,2,4,1,3]
set_option maxHeartbeats 1500000 in
private theorem cycleInvariant (x : Fin 10 → Bool) :
    target (fun i => x (cyclePetersen i)) = target x := by
  change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 1) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
      (x 4 && x 9) || (x 0 && x 5) || (x 6 && x 8) || (x 8 && x 5) ||
      (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6)) = target x
  simp only [target, Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem twistInvariant (x : Fin 10 → Bool) :
    target (fun i => x (twistPetersen i)) = target x := by
  change ((x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) ||
      (x 8 && x 5) || (x 5 && x 0) || (x 7 && x 2) || (x 9 && x 4) ||
      (x 6 && x 1) || (x 8 && x 3) || (x 0 && x 4) || (x 4 && x 3) ||
      (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0)) = target x
  simp only [target, Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private def rotationCount (v : Fin 10) : ℕ :=
  (5 - (if v.val < 5 then v.val else (twistPetersen v).val)) % 5

def toZero (v i : Fin 10) : Fin 10 :=
  (cyclePetersen^[rotationCount v]) (if v.val < 5 then i else twistPetersen i)

theorem toZero_self : ∀ v : Fin 10, toZero v v = 0 := by
  decide +kernel

private theorem cycleIterateInvariant (n : ℕ) (x : Fin 10 → Bool) :
    target (fun i => x ((cyclePetersen^[n]) i)) = target x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    exact (cycleInvariant (fun i => x ((cyclePetersen^[n]) i))).trans ih

theorem target_toZero (v : Fin 10) (x : Fin 10 → Bool) :
    target (fun i => x (toZero v i)) = target x := by
  by_cases h : v.val < 5
  · simpa only [toZero, if_pos h] using cycleIterateInvariant (rotationCount v) x
  · simpa only [toZero, if_neg h] using
      (twistInvariant (fun i => x ((cyclePetersen^[rotationCount v]) i))).trans
        (cycleIterateInvariant (rotationCount v) x)

def restricted (r : Row) : Fin 10 → Bool :=
  ![false, sample r 4, sample r 0, sample r 1, sample r 6,
    sample r 7, sample r 3, sample r 5, sample r 2, sample r 8]

def original : List (Wire Row) := inputs.map observe

private theorem availablePrimary (i : Fin 10) :
    Available false original (fun r => restricted r i) := by
  have col (j : Fin 9) : Available false original (fun r => sample r j) := by
    have inList : j.val < inputs.length := by
      have same : inputs.length = 9 := rfl
      rw [same]
      exact j.isLt
    left
    unfold original
    refine List.mem_map.mpr ⟨inputs[j.val], List.getElem_mem inList, ?_⟩
    funext r
    exact (congrArg (bit r) (List.getD_eq_getElem _ _ inList)).symm
  fin_cases i
  · exact Or.inr (Or.inl ⟨false,rfl⟩)
  · exact col 4
  · exact col 0
  · exact col 1
  · exact col 6
  · exact col 7
  · exact col 3
  · exact col 5
  · exact col 2
  · exact col 8

def restrictedAll (v : Fin 10) (r : Row) (i : Fin 10) : Bool :=
  restricted r (toZero v i)

theorem restrictedAll_self (v : Fin 10) (r : Row) : restrictedAll v r v = false := by
  change restricted r (toZero v v) = false
  rw [toZero_self] <;> rfl

private theorem cofactorCorrect (r : Row) : target (restricted r) = observe graph r := by
  have table : observe graph r = edge (sample r) := edge_table r
  rw [table]
  let x := sample r
  change ((false && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && false) ||
      (false && x 7) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) ||
      (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7)) = edge x
  simp only [edge, Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false,
    Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

theorem allCofactorCorrect (v : Fin 10) (r : Row) :
    target (restrictedAll v r) = observe graph r :=
  (target_toZero v (restricted r)).trans (cofactorCorrect r)

private theorem monoLower : Lower false inputs graph 16 := by
  apply lower_impossible graph_proper (by decide +kernel) (by decide +kernel) ?_ monoRoot
  intro a member
  rw [←input_list] at member
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  refine ⟨absentRow670 i,presentRow670 i,requiredInputs.1 i,?_⟩
  intro b hb distinct
  rw [←input_list] at hb
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  exact requiredInputs.2 i j (fun eq => distinct (by rw [eq]))

def zeroColumn {R : Type} : Wire R := fun _ => false

def seedValues (k : Fin 12) (useHint : Bool) (x : Fin 10 → Bool) : List Bool :=
  (List.ofFn x ++ [if useHint then x 0 && x 2 else false]) ++
    [!(NotBudget.base x).getD k.val false]

def seedColumns (k : Fin 12) (useHint : Bool) (v : Fin 10) : List (Wire Row) :=
  (List.ofFn (fun (i : Fin 10) r => restrictedAll v r i) ++
    [fun r => if useHint then restrictedAll v r 0 && restrictedAll v r 2 else false]) ++
    [fun r => !(NotBudget.base (restrictedAll v r)).getD k.val false]

@[simp] theorem seedColumns_length (k : Fin 12) (useHint : Bool) (v : Fin 10) :
    (seedColumns k useHint v).length = 12 := by simp [seedColumns]

theorem seedColumns_at (k : Fin 12) (useHint : Bool) (v : Fin 10) (r : Row) :
    (seedColumns k useHint v).map (fun f => f r) = seedValues k useHint (restrictedAll v r) := by
  simp only [seedColumns,seedValues,List.map_append,List.map_singleton,List.map_ofFn,Function.comp_def] <;> rfl

def column {R : Type} (ws : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map fun i => (ws.getD i zeroColumn) r)

private def afterColumns {R : Type} (seed : List (Wire R)) :
    List Gate → List (Wire R) → List (Wire R)
  | [], past => past
  | g :: gs, past => afterColumns seed gs (past ++ [column (seed ++ past) g])

def prefixColumns {R : Type} (seed : List (Wire R)) (gs : List Gate) : List (Wire R) :=
  seed ++ afterColumns seed gs []

def Free {R : Type} (ws : List (Wire R)) (g : Gate) : Prop :=
  g.inputs.length ≤ 1 ∨ (∃ i, g.inputs = [i,i]) ∨
    ∃ i ∈ g.inputs, Constant (ws.getD i zeroColumn)

private theorem column_at {R : Type} (ws : List (Wire R)) (g : Gate) (r : R) :
    column ws g r = g.op.eval (g.inputs.map fun i => (ws.map (fun f => f r)).getD i false) := by
  unfold column
  congr 1
  apply List.map_congr_left
  intro i _
  exact (List.getD_map (l := ws) (n := i) (d := zeroColumn) (fun f : Wire R => f r)).symm

private theorem afterColumns_at {R : Type} (seed past : List (Wire R)) (gs : List Gate) (r : R) :
    (seed ++ afterColumns seed gs past).map (fun f => f r) =
      (⟨gs,0⟩ : Circuit).wires ((seed ++ past).map (fun f => f r)) := by
  induction gs generalizing past with
  | nil => rfl
  | cons g gs ih =>
    change (seed ++ afterColumns seed gs (past ++ [column (seed ++ past) g])).map
        (fun f => f r) =
      (⟨gs,0⟩ : Circuit).wires (((seed ++ past).map (fun f => f r)) ++
        [g.op.eval (g.inputs.map fun i => ((seed ++ past).map (fun f => f r)).getD i false)])
    rw [ih]
    simp only [List.append_assoc,List.map_append,List.map_singleton,column_at]

theorem prefix_at {R : Type} (seed : List (Wire R)) (gs : List Gate) (r : R) :
    (prefixColumns seed gs).map (fun f => f r) = (⟨gs,0⟩ : Circuit).wires (seed.map (fun f => f r)) := by
  simpa only [prefixColumns,List.append_nil] using afterColumns_at seed [] gs r

private theorem readAvailable {R : Type} {seed past bank : List (Wire R)}
    (havePast : supply false bank past) (i : ℕ)
    (primary : i < seed.length → Available false bank (seed.getD i zeroColumn)) :
    Available false bank ((seed ++ past).getD i zeroColumn) := by
  by_cases h : i < seed.length
  · rw [List.getD_append _ _ _ _ h]
    exact primary h
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt h),List.getD_eq_getElem?_getD]
    cases found : past[i - seed.length]? with
    | none => exact Or.inr (Or.inl ⟨false,rfl⟩)
    | some w => exact havePast w (List.mem_of_getElem? found)

private theorem appendSupply {R : Type} {bank past : List (Wire R)} {w : Wire R}
    (old : supply false bank past) (new : Available false bank w) :
    supply false bank (past ++ [w]) := by
  intro f h
  rcases List.mem_append.mp h with hp | hw
  · exact old f hp
  · rw [List.mem_singleton.mp hw]
    exact new

private theorem advance {R : Type} {roots bank : List (Wire R)} {used : ℕ}
    (ws : List (Wire R)) (g : Gate) (save : Bool) (reach : Reach false roots used bank)
    (hop : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2)
    (ready : ∀ i ∈ g.inputs, Available false bank (ws.getD i zeroColumn))
    (free : save = true → Free ws g) :
    ∃ spent next, Reach false roots spent next ∧ Available false next (column ws g) ∧
      (∀ w, Available false bank w → Available false next w) ∧
      spent + (if save then 1 else 0) ≤ used + 1 := by
  have retain (h : Available false bank (column ws g)) :
      ∃ spent next, Reach false roots spent next ∧ Available false next (column ws g) ∧
        (∀ w, Available false bank w → Available false next w) ∧
        spent + (if save then 1 else 0) ≤ used + 1 :=
    ⟨used,bank,reach,h,fun _ h => h, by cases save <;> simp⟩
  cases pins : g.inputs with
  | nil =>
    apply retain
    exact Or.inr (Or.inl ⟨g.op.eval [],by funext r; simp [column,pins]⟩)
  | cons a tail =>
    cases tail with
    | nil =>
      apply retain
      have same : column ws g = ws.getD a zeroColumn := by
        funext r
        rcases hop with h | h <;> simp [column,pins,h,GateOp.eval]
      rw [same]
      exact ready a (by simp [pins])
    | cons b tail =>
      cases tail with
      | nil =>
        let aCol := ws.getD a zeroColumn
        let bCol := ws.getD b zeroColumn
        let op := !(g.op.eval [])
        have same : column ws g = combine op aCol bCol := by
          funext r
          rcases hop with h | h <;> simp [column,pins,op,combine,h,GateOp.eval,aCol,bCol]
        have ha := ready a (by simp [pins])
        have hb := ready b (by simp [pins])
        by_cases hs : save = true
        · apply retain
          rcases free hs with short | repeated | ⟨i,hm,const⟩
          · simp [pins] at short
          · obtain ⟨i,eq⟩ := repeated
            have samePins : a = i ∧ b = i := by simpa [pins] using eq
            have ab : a = b := samePins.1.trans samePins.2.symm
            have sameCol : column ws g = aCol := by
              rw [same]
              funext r
              simp [aCol,bCol,ab,combine]
            rw [sameCol]
            exact ha
          · rw [same]
            simp only [pins,List.mem_cons,List.mem_nil_iff,or_false] at hm
            rcases hm with rfl | rfl
            · exact from_constant op (Or.inl const) ha hb
            · exact from_constant op (Or.inr const) ha hb
        · refine ⟨used+1,column ws g :: bank,?_,Or.inl List.mem_cons_self,
            fun _ h => available_cons _ h, by simp [hs]⟩
          rw [same]
          exact Reach.two op reach ha hb
      | cons c after =>
        simp [pins] at arity <;> omega

private theorem simulate {R : Type} (seed : List (Wire R)) (save : ℕ → Bool) (start : ℕ)
    (gs : List Gate) {roots bank past : List (Wire R)} {used : ℕ}
    (reach : Reach false roots used bank) (havePast : supply false bank past)
    (model : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (ready : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < seed.length →
      Available false bank (seed.getD i zeroColumn))
    (fixed : ∀ before g after, gs = before ++ g :: after → save (start + before.length) = true →
      Free (seed ++ afterColumns seed before past) g) :
    ∃ spent next, Reach false roots spent next ∧
      supply false next (afterColumns seed gs past) ∧
      spent + (gs.zipIdx start).countP (fun row => save row.2) ≤ used + gs.length := by
  induction gs generalizing start used bank past with
  | nil => exact ⟨used,bank,reach,havePast,by simp⟩
  | cons g gs ih =>
    have hg := model g List.mem_cons_self
    have h (marked : save start = true) : Free (seed ++ past) g :=
      fixed [] g gs rfl (by simpa using marked)
    obtain ⟨mid,bank',reach',value,keep,cost⟩ :=
      advance (seed ++ past) g (save start) reach hg.1 hg.2
        (fun i hi => readAvailable havePast i (ready g List.mem_cons_self i hi)) h
    have havePast' : supply false bank' (past ++ [column (seed ++ past) g]) :=
      appendSupply (fun w hw => keep w (havePast w hw)) value
    obtain ⟨spent,next,reachable,supplied,budget⟩ :=
      ih (start := start+1) reach' havePast'
        (fun w hw => model w (List.mem_cons_of_mem _ hw))
        (fun w hw i hi before => keep _ (ready w (List.mem_cons_of_mem _ hw) i hi before))
        (fun before w after eq marked => by
          have same : g :: gs = (g :: before) ++ w :: after := congrArg (List.cons g) eq
          have startEq : start + (g :: before).length = start + 1 + before.length := by simp; omega
          exact fixed (g :: before) w after same (by rwa [startEq]))
    refine ⟨spent,next,reachable,supplied,?_⟩
    simp only [List.zipIdx_cons,List.countP_cons,List.length_cons]
    cases hs : save start <;> simp [hs] at cost ⊢ <;> omega

private theorem countPByIndex {α : Type} (p : α → Bool) :
    ∀ l : List α, l.countP p =
      (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card
  | [] => by simp
  | a :: l => by
    have ih := countPByIndex p l
    have split : (Finset.univ.filter fun i : Fin (a :: l).length => p ((a :: l).get i) = true).card =
        (if p a = true then 1 else 0) +
          (Finset.univ.filter fun i : Fin l.length => p (l.get i) = true).card := by
      rw [show (Finset.univ.filter fun i : Fin (a :: l).length => p ((a :: l).get i) = true).card =
          (Finset.univ.filter fun i : Fin (l.length + 1) => p ((a :: l).get i) = true).card from rfl,
        Fin.card_filter_univ_succ (n := l.length) (fun i : Fin (l.length + 1) => p ((a :: l).get i) = true)]
      by_cases h : p a = true
      · simp [h, Function.comp_def, add_comm]
      · simp [h, Function.comp_def]
    rw [split, ← ih, List.countP_cons, add_comm]

def ReadsInput (C : Circuit) (i : ℕ) : Prop := ∃ g ∈ C.gates, i ∈ g.inputs

def Ready (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10) : Prop :=
  ∀ i < 12, ReadsInput C i →
    Available false original ((seedColumns k useHint v).getD i zeroColumn)

theorem seed_literal (k : Fin 12) (useHint : Bool) (v i : Fin 10) :
    (seedColumns k useHint v).getD i.val zeroColumn = fun r => restrictedAll v r i := by
  have bound := i.isLt
  unfold seedColumns
  rw [List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using bound),
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using bound),List.getElem_ofFn] <;> rfl

theorem seed_literal_available (k : Fin 12) (useHint : Bool) (v i : Fin 10) :
    Available false original ((seedColumns k useHint v).getD i.val zeroColumn) := by
  rw [seed_literal]
  exact availablePrimary (toZero v i)

theorem seed_hint (k : Fin 12) (useHint : Bool) (v : Fin 10) :
    (seedColumns k useHint v).getD 10 zeroColumn =
      fun r => if useHint then restrictedAll v r 0 && restrictedAll v r 2 else false := by
  unfold seedColumns
  rw [List.getD_append _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)] <;> simp

theorem seed_neg (k : Fin 12) (useHint : Bool) (v : Fin 10) :
    (seedColumns k useHint v).getD 11 zeroColumn =
      fun r => !(NotBudget.base (restrictedAll v r)).getD k.val false := by
  unfold seedColumns
  rw [List.getD_append_right _ _ _ _ (by simp)] <;> simp

theorem constant_literal (k : Fin 12) (useHint : Bool) (v : Fin 10) :
    Constant ((seedColumns k useHint v).getD v.val zeroColumn) := by
  rw [seed_literal]
  exact ⟨false,funext (restrictedAll_self v)⟩

theorem constant_hint (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (fixed : useHint = false ∨ v = 0 ∨ v = 2) :
    Constant ((seedColumns k useHint v).getD 10 zeroColumn) := by
  rw [seed_hint]
  refine ⟨false,?_⟩
  funext r
  rcases fixed with off | rfl | rfl
  · simp [off]
  · simp [restrictedAll_self]
  · simp [restrictedAll_self]

private theorem base_primary (x : Fin 10 → Bool) (v : Fin 10) :
    (NotBudget.base x).getD v.val false = x v := by
  have bound := v.isLt
  unfold NotBudget.base
  rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using bound),
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using bound),List.getElem_ofFn] <;> rfl

private theorem base_hint (x : Fin 10 → Bool) :
    (NotBudget.base x).getD 10 false = (x 0 && x 2) := by
  unfold NotBudget.base
  rw [List.getD_append_right _ _ _ _ (by simp)] <;> simp

theorem constant_neg (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (fixed : k.val = v.val ∨ k.val = 11 ∨ (k.val = 10 ∧ (v = 0 ∨ v = 2))) :
    Constant ((seedColumns k useHint v).getD 11 zeroColumn) := by
  rw [seed_neg]
  refine ⟨true,?_⟩
  funext r
  rcases fixed with atV | outside | ⟨atHint, endpoint⟩
  · rw [atV,base_primary,restrictedAll_self] <;> rfl
  · rw [outside,List.getD_eq_default _ _ (by simp [NotBudget.base])] <;> rfl
  · rw [atHint,base_hint]
    rcases endpoint with rfl | rfl <;> simp [restrictedAll_self]

theorem seed_ready (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (goodHint : (useHint = false ∨ v = 0 ∨ v = 2) ∨ ¬ReadsInput C 10)
    (goodNeg : (k.val = v.val ∨ k.val = 11 ∨ (k.val = 10 ∧ (v = 0 ∨ v = 2))) ∨
      ¬ReadsInput C 11) :
    Ready C k useHint v := by
  intro i bound usedHere
  by_cases small : i < 10
  · let j : Fin 10 := ⟨i,small⟩
    change Available false original ((seedColumns k useHint v).getD j.val zeroColumn)
    rw [seed_literal]
    exact availablePrimary (toZero v j)
  · by_cases equal : i = 10
    · subst i
      exact goodHint.elim (fun h => Or.inr (Or.inl (constant_hint k useHint v h)))
        (fun h => (h usedHere).elim)
    · have is11 : i = 11 := by omega
      subst i
      exact goodNeg.elim (fun h => Or.inr (Or.inl (constant_neg k useHint v h)))
        (fun h => (h usedHere).elim)

private theorem afterColumns_append {R : Type} (seed past : List (Wire R)) (a b : List Gate) :
    afterColumns seed (a ++ b) past = afterColumns seed b (afterColumns seed a past) := by
  induction a generalizing past with
  | nil => rfl
  | cons g gs ih => exact ih _

private theorem afterColumns_extends {R : Type} (seed past : List (Wire R)) (gs : List Gate) :
    ∃ tail, afterColumns seed gs past = past ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing past with
  | nil => exact ⟨[],by simp [afterColumns],rfl⟩
  | cons g gs ih =>
    obtain ⟨tail,h,hlen⟩ := ih (past ++ [column (seed ++ past) g])
    exact ⟨column (seed ++ past) g :: tail,by simpa [afterColumns,List.append_assoc] using h,
      by simp [hlen]⟩

theorem prefix_length {R : Type} (seed : List (Wire R)) (gs : List Gate) :
    (prefixColumns seed gs).length = seed.length + gs.length := by
  obtain ⟨tail,eq,size⟩ := afterColumns_extends seed [] gs
  simp [prefixColumns,eq,size]

theorem prefix_getAtGate {R : Type} (seed : List (Wire R)) (gs : List Gate) (i : Fin gs.length) :
    (prefixColumns seed gs).getD (seed.length+i.val) zeroColumn =
      column (prefixColumns seed (gs.take i.val)) (gs.get i) := by
  let before := gs.take i.val
  let after := gs.drop (i.val+1)
  let g := gs.get i
  let prior := afterColumns seed before []
  let value := column (seed ++ prior) g
  have split : gs = before ++ g :: after := by simp [before,g,after]
  have forTail := afterColumns_extends seed (prior ++ [value]) after
  obtain ⟨tail,eq,_⟩ := forTail
  have full : prefixColumns seed gs = ((seed ++ prior) ++ [value]) ++ tail := by
    unfold prefixColumns
    conv_lhs => rw [split,afterColumns_append]
    change seed ++ afterColumns seed after (prior ++ [value]) = _
    simp [eq,List.append_assoc]
  have width : (seed ++ prior).length = seed.length+i.val := by
    change (prefixColumns seed (gs.take i.val)).length = _
    simp [prefix_length,Nat.min_eq_left i.isLt.le]
  have longer : ((seed ++ prior) ++ [value]).length = seed.length+i.val+1 := by
    rw [List.length_append, width, List.length_singleton]
  rw [full,List.getD_append _ _ _ _ (by omega),← width]
  change ((seed ++ prior) ++ [value]).getD (seed ++ prior).length zeroColumn = value
  simp

private theorem indexedTwo (gs : List Gate) (save : ℕ → Bool) (i j : Fin gs.length)
    (distinct : i ≠ j) (hi : save i.val = true) (hj : save j.val = true) :
    2 ≤ (gs.zipIdx 0).countP (fun row => save row.2) := by
  rw [countPByIndex]
  let a : Fin (gs.zipIdx 0).length := ⟨i.val,by simpa using i.isLt⟩
  let b : Fin (gs.zipIdx 0).length := ⟨j.val,by simpa using j.isLt⟩
  have ha : save ((gs.zipIdx 0).get a).2 = true := by
    change save ((gs.zipIdx 0)[i.val]).2 = true
    simpa only [List.getElem_zipIdx,Nat.zero_add] using hi
  have hb : save ((gs.zipIdx 0).get b).2 = true := by
    change save ((gs.zipIdx 0)[j.val]).2 = true
    simpa only [List.getElem_zipIdx,Nat.zero_add] using hj
  exact Finset.one_lt_card.mpr
    ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,
      b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,
      fun h => distinct (Fin.ext (congrArg (fun z : Fin (gs.zipIdx 0).length => z.val) h))⟩

theorem cofactorFloorTwo (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (mono : Monotone2 C) (outGate : 12 ≤ C.output) (ready : Ready C k useHint v)
    (fits : ∀ x, C.eval (seedValues k useHint x) = target x)
    (i j : Fin C.gates.length) (distinct : i ≠ j)
    (freeI : Free (prefixColumns (seedColumns k useHint v) (C.gates.take i.val)) (C.gates.get i))
    (freeJ : Free (prefixColumns (seedColumns k useHint v) (C.gates.take j.val)) (C.gates.get j)) :
    18 ≤ C.size := by
  let seed := seedColumns k useHint v
  let save : ℕ → Bool := fun index => decide (index = i.val ∨ index = j.val)
  have model (g : Gate) (member : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g member
  obtain ⟨spent,bank,reach,supplyPast,count⟩ := simulate seed save 0 C.gates
    (roots := original) (past := []) Reach.start (by simp [supply]) model
    (fun g member pin hp bound => ready pin (by simpa [seed] using bound) ⟨g,member,hp⟩)
    (by
      intro before g after split marked
      have flags : before.length = i.val ∨ before.length = j.val := by simpa [save] using marked
      have reindex (idx : Fin C.gates.length) (atIdx : before.length = idx.val)
          (isFree : Free (prefixColumns seed (C.gates.take idx.val)) (C.gates.get idx)) :
          Free (seed ++ afterColumns seed before []) g := by
        have takeEq : C.gates.take idx.val = before :=
          (congrArg (fun l : List Gate => l.take idx.val) split).trans (List.take_left' atIdx)
        have gateEq : C.gates.get idx = g := by
          apply Option.some.inj
          calc
            some (C.gates.get idx) = C.gates[idx.val]? := (List.getElem?_eq_getElem idx.isLt).symm
            _ = (before ++ g :: after)[idx.val]? :=
              congrArg (fun l : List Gate => l[idx.val]?) split
            _ = some g := by
              rw [List.getElem?_append_right (by omega),atIdx,Nat.sub_self] <;> rfl
        simpa only [takeEq,gateEq,prefixColumns] using isFree
      exact flags.elim (fun h => reindex i h freeI) (fun h => reindex j h freeJ))
  have outReady : Available false bank ((prefixColumns seed C.gates).getD C.output zeroColumn) :=
    readAvailable supplyPast C.output (by
      intro tooEarly
      have len : seed.length = 12 := seedColumns_length k useHint v
      omega)
  have evaluates : (prefixColumns seed C.gates).getD C.output zeroColumn = observe graph := by
    funext r
    have same := List.getD_map (l := prefixColumns seed C.gates)
      (n := C.output) (d := zeroColumn) (fun f : Wire Row => f r)
    rw [prefix_at] at same
    change C.eval (seed.map (fun f => f r)) =
      ((prefixColumns seed C.gates).getD C.output zeroColumn) r at same
    rw [show seed.map (fun f => f r) = seedValues k useHint (restrictedAll v r) from
      seedColumns_at k useHint v r] at same
    exact same.symm.trans ((fits _).trans (allCofactorCorrect v r))
  rw [evaluates] at outReady
  have lower := monoLower spent bank reach outReady
  have twice := indexedTwo C.gates save i j distinct (by simp [save]) (by simp [save])
  change 18 ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_18007.RawCofactor

namespace PEqualNP.Outside.L_meta_18007.RawCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.NotBudget (target base)
open PEqualNP.Outside.L_meta_18007.RawCofactor

abbrev GateIndex (C : Circuit) := Fin C.gates.length

def Reads (C : Circuit) (i : GateIndex C) (input : ℕ) : Prop :=
  input ∈ (C.gates.get i).inputs

def ReadsOneOf (C : Circuit) (i : GateIndex C) (pins : Finset ℕ) : Prop :=
  ∃ a ∈ pins, Reads C i a

theorem twoReadersOrUnique (C : Circuit) (pins : Finset ℕ) (i : GateIndex C)
    (hi : ReadsOneOf C i pins) :
    (∃ j : GateIndex C, j ≠ i ∧ ReadsOneOf C j pins) ∨
      ∀ j : GateIndex C, ReadsOneOf C j pins → j = i := by
  classical
  by_cases another : ∃ j : GateIndex C, j ≠ i ∧ ReadsOneOf C j pins
  · exact .inl another
  · refine .inr fun j hj => ?_
    by_contra distinct
    exact another ⟨j, distinct, hj⟩

theorem connectsExactly {g : Gate} {p q : ℕ} (arity : g.inputs.length ≤ 2)
    (hp : p ∈ g.inputs) (hq : q ∈ g.inputs) (different : p ≠ q) :
    g.inputs = [p,q] ∨ g.inputs = [q,p] := by
  have enough : 1 < g.inputs.toFinset.card :=
    Finset.one_lt_card.mpr ⟨p,List.mem_toFinset.mpr hp,q,List.mem_toFinset.mpr hq,different⟩
  have len := List.toFinset_card_le (l := g.inputs)
  have exactly : g.inputs.length = 2 := by omega
  obtain ⟨a,b,h⟩ := List.length_eq_two.mp exactly
  rw [h] at hp hq ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (different rfl).elim
  · exact .inl rfl
  · exact .inr rfl
  · exact (different rfl).elim

theorem monoGate (C : Circuit) (mono : Monotone2 C) (i : GateIndex C) :
    ((C.gates.get i).op = .and ∨ (C.gates.get i).op = .or) ∧
      (C.gates.get i).inputs.length ≤ 2 := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using mono _ (List.get_mem C.gates i)

theorem inputPrimary (k : Fin 12) (useHint : Bool) (x : Fin 10 → Bool) (v : Fin 10) :
    (seedValues k useHint x).getD v.val false = x v := by
  unfold seedValues
  rw [List.getD_append _ _ _ _ (by simp; have := v.isLt; omega)]
  rw [List.getD_append _ _ _ _ (by simpa using v.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using v.isLt), List.getElem_ofFn] <;> rfl

theorem inputHint (k : Fin 12) (useHint : Bool) (x : Fin 10 → Bool) :
    (seedValues k useHint x).getD 10 false = (if useHint then x 0 && x 2 else false) := by
  simp [seedValues, List.getD_append_right, List.getD_append]

theorem inputNegated (k : Fin 12) (useHint : Bool) (x : Fin 10 → Bool) :
    (seedValues k useHint x).getD 11 false = !((base x).getD k.val false) := by
  simp [seedValues, List.getD_append_right, List.getD_append]

theorem negatedPrimary (k : Fin 12) (useHint : Bool) (x : Fin 10 → Bool)
    (v : Fin 10) (atV : k.val = v.val) :
    (seedValues k useHint x).getD 11 false = !(x v) := by
  rw [inputNegated, atV]
  unfold base
  rw [List.getD_append _ _ _ _ (by simpa using v.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using v.isLt), List.getElem_ofFn] <;> rfl

theorem negatedHint (useHint : Bool) (x : Fin 10 → Bool) :
    (seedValues 10 useHint x).getD 11 false = !(x 0 && x 2) := by
  rw [inputNegated]
  simp [base, List.getD_append_right]

theorem negatedMissing (useHint : Bool) (x : Fin 10 → Bool) :
    (seedValues 11 useHint x).getD 11 false = true := by
  rw [inputNegated]
  have beyond : (base x).length ≤ (11 : Fin 12).val := by simp [base]
  rw [List.getD_eq_default _ _ beyond]
  rfl

theorem inputCases (k : Fin 12) (useHint : Bool) (x : Fin 10 → Bool)
    (a : ℕ) (ha : a < 12) :
    (∃ v : Fin 10, a = v.val ∧ (seedValues k useHint x).getD a false = x v) ∨
      a = 10 ∨ a = 11 := by
  by_cases h : a < 10
  · exact .inl ⟨⟨a,h⟩,rfl,inputPrimary k useHint x ⟨a,h⟩⟩
  · right
    omega

theorem evalTwoPins (g : Gate) (op : g.op = .and ∨ g.op = .or)
    (x : ℕ → Bool) {p q : ℕ} (form : g.inputs = [p,q] ∨ g.inputs = [q,p]) :
    g.op.eval (g.inputs.map x) = (match g.op with
      | .or => x p || x q
      | _ => x p && x q) := by
  rcases op with isAnd | isOr
  · rcases form with same | reverse
    · simp [isAnd, same, GateOp.eval]
    · simp [isAnd, reverse, GateOp.eval, Bool.and_comm]
  · rcases form with same | reverse
    · simp [isOr, same, GateOp.eval]
    · simp [isOr, reverse, GateOp.eval, Bool.or_comm]

end PEqualNP.Outside.L_meta_18007.RawCases

namespace PEqualNP.Outside.L_meta_18007.RawCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.NotBudget (target)
open PEqualNP.Outside.L_meta_18007.RawCofactor

theorem dependenceWithFixedHint (v : Fin 10) :
    ∃ x y : Fin 10 → Bool, x v = false ∧ y v = true ∧
      (∀ i, i ≠ v → x i = y i) ∧ (x 0 && x 2) = (y 0 && y 2) ∧
      target x = false ∧ target y = true := by
  let q : Fin 10 := if v = 0 then 2 else 0
  have ne : v ≠ q := by
    by_cases h : v = 0
    · simp [q,h]
    · simpa [q,h] using h
  obtain ⟨x,y,xv,yv,xq,yq,agree,off,on⟩ := Dependence.dependence_at_value v q ne false
  refine ⟨x,y,xv,yv,agree,?_,off,on⟩
  by_cases h : v = 0
  · simp [q,h] at xq yq
    simp [xq,yq]
  · simp [q,h] at xq yq
    simp [xq,yq]

theorem nonprimarySeedCases (k : Fin 12) (h : ¬k.val < 10) : k = 10 ∨ k = 11 := by
  have bound := k.isLt
  by_cases h10 : k.val = 10
  · exact Or.inl (Fin.ext h10)
  · exact Or.inr (Fin.ext (by change k.val = 11; omega))

theorem decreasingOnOtherInputs (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (x y : Fin 10 → Bool) (xv : x v = false) (yv : y v = true)
    (agree : ∀ i, i ≠ v → x i = y i) (hint : (x 0 && x 2) = (y 0 && y 2))
    (a : ℕ) (ha : a < 12) (different : a ≠ v.val) :
    (seedValues k useHint y).getD a false ≤ (seedValues k useHint x).getD a false := by
  rcases inputCases k useHint y a ha with ⟨i,rfl,_⟩ | rfl | rfl
  · rw [inputPrimary, inputPrimary, agree i]
    intro eq
    exact different (congrArg Fin.val eq)
  · rw [inputHint,inputHint,hint]
  · by_cases hk : k.val < 10
    · let u : Fin 10 := ⟨k.val,hk⟩
      rw [negatedPrimary k useHint y u rfl, negatedPrimary k useHint x u rfl]
      by_cases hu : u = v
      · rw [hu,xv,yv]
        decide
      · rw [agree u hu]
    · rcases nonprimarySeedCases k hk with rfl | rfl
      · rw [negatedHint, negatedHint, hint]
      · rw [negatedMissing, negatedMissing]

theorem agreeAwayFromPins (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (x y : Fin 10 → Bool) (agree : ∀ i, i ≠ v → x i = y i)
    (pin : ℕ) (inRange : pin < 12) (primary : pin ≠ v.val)
    (hint : pin = 10 → (if useHint then x 0 && x 2 else false) =
                         (if useHint then y 0 && y 2 else false))
    (negated : pin = 11 → (seedValues k useHint x).getD 11 false =
                          (seedValues k useHint y).getD 11 false) :
    (seedValues k useHint x).getD pin false = (seedValues k useHint y).getD pin false := by
  rcases inputCases k useHint x pin inRange with ⟨i,rfl,_⟩ | rfl | rfl
  · rw [inputPrimary, inputPrimary]
    exact agree i (fun eq => primary (congrArg Fin.val eq))
  · rw [inputHint, inputHint]
    exact hint rfl
  · exact negated rfl

end PEqualNP.Outside.L_meta_18007.RawCases

namespace PEqualNP.Outside.L_meta_18007.RawCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.NotBudget (target)
open PEqualNP.Outside.L_meta_18007.RawCofactor

theorem inputLength (k : Fin 12) (useHint : Bool) (x : Fin 10 → Bool) :
    (seedValues k useHint x).length = 12 := by simp [seedValues]

def Fits (C : Circuit) (k : Fin 12) (useHint : Bool) : Prop :=
  ∀ x, C.eval (seedValues k useHint x) = target x

theorem fitOutputAtGate (C : Circuit) (k : Fin 12) (useHint : Bool) (fits : Fits C k useHint) :
    12 ≤ C.output ∧ C.output < 12 + C.gates.length := by
  have lo : 12 ≤ C.output := by
    by_contra below
    have idx : C.output < 12 := by omega
    have read (x : Fin 10 → Bool) : (seedValues k useHint x).getD C.output false = target x := by
      have ev := fits x
      change (C.wires (seedValues k useHint x)).getD C.output false = target x at ev
      rwa [RawWires.wires_input C _ _ (by simpa [inputLength] using idx)] at ev
    rcases inputCases k useHint (fun _ => false) C.output idx with ⟨v,hv,_⟩ | hint | neg
    · obtain ⟨x,diff⟩ := Dependence.target_not_signed_primary v false
      have h := read x
      rw [hv,inputPrimary] at h
      exact diff (by simpa using h.symm)
    · cases useHint
      · obtain ⟨x,diff⟩ := Dependence.target_not_constant false
        have h := read x
        rw [hint,inputHint] at h
        exact diff (by simpa using h.symm)
      · obtain ⟨x,diff⟩ := Dependence.target_not_signed_hint false
        have h := read x
        rw [hint,inputHint] at h
        exact diff (by simpa using h.symm)
    · by_cases hk : k.val < 10
      · let v : Fin 10 := ⟨k.val,hk⟩
        obtain ⟨x,diff⟩ := Dependence.target_not_signed_primary v true
        have h := read x
        rw [neg,negatedPrimary k useHint x v rfl] at h
        exact diff (by simpa using h.symm)
      · rcases nonprimarySeedCases k hk with rfl | rfl
        · obtain ⟨x,diff⟩ := Dependence.target_not_signed_hint true
          have h := read x
          rw [neg,negatedHint] at h
          exact diff (by simpa using h.symm)
        · obtain ⟨x,diff⟩ := Dependence.target_not_constant true
          have h := read x
          rw [neg,negatedMissing] at h
          exact diff h.symm
  refine ⟨lo,?_⟩
  by_contra above
  obtain ⟨x,diff⟩ := Dependence.target_not_constant false
  have ev := fits x
  change (C.wires (seedValues k useHint x)).getD C.output false = target x at ev
  rw [List.getD_eq_default _ _ (by rw [RawWires.wires_length, inputLength]; omega)] at ev
  exact diff ev.symm

theorem positiveReader (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (mono : Monotone2 C) (fits : Fits C k useHint) :
    ∃ i : GateIndex C, Reads C i v.val := by
  by_contra no
  obtain ⟨x,y,xv,yv,agree,hint,off,on⟩ := dependenceWithFixedHint v
  have order := RawWires.eval_true_of_read_monotonicity C (seedValues k useHint y)
    (seedValues k useHint x) (by simp [inputLength])
    (by simpa [inputLength] using (fitOutputAtGate C k useHint fits).1)
    (fun g hg => by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (mono g hg).1)
    (by
      intro j hj t ht htSmall htrue
      have ne : t ≠ v.val := by
        rintro rfl
        exact no ⟨⟨j,hj⟩,ht⟩
      have le := decreasingOnOtherInputs k useHint v x y xv yv agree hint t
        (by simpa [inputLength] using htSmall) ne
      rw [htrue] at le
      exact Bool.eq_true_of_true_le le)
    ((fits y).trans on)
  rw [fits x,off] at order
  exact Bool.false_ne_true order

theorem equalAtGateOnInitialPins (C : Circuit) (k : Fin 12) (useHint : Bool)
    (i : GateIndex C) (x y : Fin 10 → Bool)
    (initial : ∀ a ∈ (C.gates.get i).inputs, a < 12)
    (same : (C.gates.get i).op.eval ((C.gates.get i).inputs.map fun a =>
      (seedValues k useHint x).getD a false) =
      (C.gates.get i).op.eval ((C.gates.get i).inputs.map fun a =>
        (seedValues k useHint y).getD a false)) :
    (C.wires (seedValues k useHint x)).getD (12 + i.val) false =
      (C.wires (seedValues k useHint y)).getD (12 + i.val) false := by
  have left := RawWires.wires_gate_of_input_reads C (seedValues k useHint x) i.val i.isLt
    (fun t ht => by simpa [inputLength] using initial t ht)
  have right := RawWires.wires_gate_of_input_reads C (seedValues k useHint y) i.val i.isLt
    (fun t ht => by simpa [inputLength] using initial t ht)
  rw [inputLength] at left right
  exact left.trans (same.trans right.symm)

theorem impossibleAgreement (C : Circuit) (k : Fin 12) (useHint : Bool)
    (fits : Fits C k useHint) (x y : Fin 10 → Bool) (off : target x = false) (on : target y = true)
    (agree : ∀ i : GateIndex C,
      (C.wires (seedValues k useHint x)).getD (12 + i.val) false =
        (C.wires (seedValues k useHint y)).getD (12 + i.val) false ∨
      ∀ t ∈ (C.gates.get i).inputs, t < 12 →
        (seedValues k useHint x).getD t false = (seedValues k useHint y).getD t false) : False := by
  have eval := RawWires.eval_eq_of_read_agreement C (seedValues k useHint x)
    (seedValues k useHint y) (by simp [inputLength])
    (by simpa [inputLength] using (fitOutputAtGate C k useHint fits).1)
    (fun i hi => by simpa [inputLength] using agree ⟨i,hi⟩)
  rw [fits x,fits y,off,on] at eval
  exact Bool.false_ne_true eval

end PEqualNP.Outside.L_meta_18007.RawCases

namespace PEqualNP.Outside.L_meta_18007.RawCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.NotBudget (target)
open PEqualNP.Outside.L_meta_18007.RawCofactor

theorem outsidePriorityPins (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (x y : Fin 10 → Bool) (agree : ∀ j, j ≠ v → x j = y j)
    (j : GateIndex C) (off : ¬ ReadsOneOf C j {v.val,10,11})
    (a : ℕ) (read : Reads C j a) (ha : a < 12) :
    (seedValues k useHint x).getD a false = (seedValues k useHint y).getD a false := by
  have away : a ∉ ({v.val,10,11} : Finset ℕ) := fun mem => off ⟨a,mem,read⟩
  have none : a ≠ v.val ∧ a ≠ 10 ∧ a ≠ 11 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using away
  exact agreeAwayFromPins k useHint v x y agree a ha none.1
    (fun eq => (none.2.1 eq).elim) (fun eq => (none.2.2 eq).elim)

theorem evalAtPins (C : Circuit) (k : Fin 12) (useHint : Bool) (mono : Monotone2 C)
    (i : GateIndex C) (x : Fin 10 → Bool) {p q : ℕ} (hp : p < 12) (hq : q < 12)
    (form : (C.gates.get i).inputs = [p,q] ∨ (C.gates.get i).inputs = [q,p]) :
    (C.wires (seedValues k useHint x)).getD (12 + i.val) false =
      (match (C.gates.get i).op with
        | .or => (seedValues k useHint x).getD p false || (seedValues k useHint x).getD q false
        | _ => (seedValues k useHint x).getD p false && (seedValues k useHint x).getD q false) := by
  have initial (t : ℕ) (ht : t ∈ (C.gates.get i).inputs) : t < (seedValues k useHint x).length := by
    rw [inputLength]
    rcases form with eq | eq <;> rw [eq] at ht <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    · rcases ht with rfl | rfl <;> assumption
    · rcases ht with rfl | rfl <;> assumption
  have ev := RawWires.wires_gate_of_input_reads C (seedValues k useHint x) i.val i.isLt initial
  rw [inputLength] at ev
  exact ev.trans (evalTwoPins _ (monoGate C mono i).1 _ form)

theorem onlyComplementReaderImpossible (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (index : k.val = v.val) (mono : Monotone2 C) (fits : Fits C k useHint)
    (i : GateIndex C) (untouched : ∀ j : GateIndex C, j ≠ i → ¬ ReadsOneOf C j {v.val,10,11})
    (form : (C.gates.get i).inputs = [v.val,11] ∨ (C.gates.get i).inputs = [11,v.val]) : False := by
  obtain ⟨x,y,xv,yv,agree,_,off,on⟩ := dependenceWithFixedHint v
  apply impossibleAgreement C k useHint fits x y off on
  intro j
  by_cases eq : j = i
  · subst j
    left
    have hx := evalAtPins C k useHint mono i x (by have := v.isLt; omega) (by decide) form
    have hy := evalAtPins C k useHint mono i y (by have := v.isLt; omega) (by decide) form
    rw [hx,hy,inputPrimary,inputPrimary,negatedPrimary k useHint x v index,
      negatedPrimary k useHint y v index,xv,yv]
    rcases (monoGate C mono i).1 with eq | eq <;> simp [eq]
  · exact .inr (outsidePriorityPins C k useHint v x y agree j (untouched j eq))

end PEqualNP.Outside.L_meta_18007.RawCases

namespace PEqualNP.Outside.L_meta_18007.RawCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.NotBudget (target)
open PEqualNP.Outside.L_meta_18007.RawCofactor

theorem endpointHintAlias (C : Circuit) (k : Fin 12) (v : Fin 10) (i : GateIndex C)
    (endpoint : v = 0 ∨ v = 2)
    (pins : (C.gates.get i).inputs = [v.val, 10] ∨ (C.gates.get i).inputs = [10, v.val])
    (untouched : ∀ j : GateIndex C, j ≠ i → ¬ ReadsOneOf C j {v.val, 10, 11})
    (mono : Monotone2 C) (fits : Fits C k true) :
    (∀ x : Fin 10 → Bool, (C.wires (seedValues k true x)).getD (12 + i.val) false = x v) ∧
      ∃ j : GateIndex C, i.val < j.val ∧ Reads C j (12 + i.val) := by
  obtain ⟨x,y,xv,yv,agree,hint,off,on⟩ := dependenceWithFixedHint v
  have primaryPin : v.val < 12 := by
    have := v.isLt
    omega
  have hintPin : (10 : ℕ) < 12 := by decide
  have agreeOther (j : GateIndex C) (different : j ≠ i) :=
    outsidePriorityPins C k true v x y agree j (untouched j different)
  rcases (monoGate C mono i).1 with isAnd | isOr
  · exfalso
    have andValue (z : Fin 10 → Bool) :
        (C.wires (seedValues k true z)).getD (12 + i.val) false =
          (z v && (z 0 && z 2)) := by
      rw [evalAtPins C k true mono i z primaryPin hintPin pins, isAnd, inputPrimary, inputHint] <;> rfl
    have falseHint : (x 0 && x 2) = false := by
      rcases endpoint with rfl | rfl <;> simp [xv]
    apply impossibleAgreement C k true fits x y off on
    intro j
    by_cases same : j = i
    · subst j
      left
      rw [andValue x, andValue y, ← hint, falseHint]
      simp
    · exact Or.inr (agreeOther j same)
  · have aliasesPrimary (z : Fin 10 → Bool) :
        (C.wires (seedValues k true z)).getD (12 + i.val) false = z v := by
      have value :
          (C.wires (seedValues k true z)).getD (12 + i.val) false =
            (z v || (z 0 && z 2)) := by
        rw [evalAtPins C k true mono i z primaryPin hintPin pins, isOr, inputPrimary, inputHint] <;> rfl
      rw [value]
      rcases endpoint with rfl | rfl <;> cases z 0 <;> cases z 2 <;> rfl
    have outputOther : C.output ≠ 12 + i.val := by
      intro eq
      obtain ⟨z,different⟩ := Dependence.target_not_signed_primary v false
      change target z ≠ z v at different
      apply different
      refine (fits z).symm.trans ?_
      simpa only [Circuit.eval, eq] using aliasesPrimary z
    have outputsDiffer : C.eval (seedValues k true x) ≠ C.eval (seedValues k true y) := by
      rw [fits x, fits y, off, on]
      decide
    obtain ⟨j,hj,ordered,uses⟩ := RawWires.exists_consumer_of_eval_ne C
      (seedValues k true x) (seedValues k true y) (by simp only [inputLength])
      (by simpa only [inputLength] using (fitOutputAtGate C k true fits).1) i.val
      (by simpa only [inputLength] using outputOther) outputsDiffer
      (fun j hj different a read small =>
        agreeOther ⟨j,hj⟩ (fun same => different (congrArg Fin.val same)) a read
          (by simpa only [inputLength] using small))
    exact ⟨aliasesPrimary,⟨⟨j,hj⟩,ordered,by simpa only [Reads,List.get_eq_getElem,inputLength] using uses⟩⟩

end PEqualNP.Outside.L_meta_18007.RawCases

namespace PEqualNP.Outside.L_meta_18007.RawCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.RawCofactor
open PEqualNP.Outside.L_meta_18007.NineInputs (Constant)

def InactiveExtra (C : Circuit) (k : Fin 12) (useHint : Bool) (i : ℕ) : Prop :=
  (∃ b : Bool, ∀ x, (seedValues k useHint x).getD i false = b) ∨ ¬ ReadsInput C i

private theorem fixedExtra (C : Circuit) (k : Fin 12) (useHint : Bool)
    (h10 : InactiveExtra C k useHint 10) (h11 : InactiveExtra C k useHint 11)
    (a : ℕ) (lower : 10 ≤ a) (upper : a < 12) (used : ReadsInput C a) :
    ∃ b : Bool, ∀ x, (seedValues k useHint x).getD a false = b := by
  by_cases h : a = 10
  · subst a
    exact h10.resolve_right (fun unseen => unseen used)
  · have e : a = 11 := by omega
    subst a
    exact h11.resolve_right (fun unseen => unseen used)

private theorem fixedSeedColumn (k : Fin 12) (useHint : Bool) (v : Fin 10) (pin : ℕ)
    (fixed : ∃ b : Bool, ∀ x, (seedValues k useHint x).getD pin false = b) :
    Constant ((seedColumns k useHint v).getD pin zeroColumn) := by
  obtain ⟨b,e⟩ := fixed
  refine ⟨b,?_⟩
  funext r
  have map := List.getD_map (l := seedColumns k useHint v) (n := pin)
    (d := zeroColumn) (fun f => f r)
  rw [seedColumns_at] at map
  exact map.symm.trans (e (restrictedAll v r))

theorem freeAtSeedPin (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (i : GateIndex C) (a : ℕ) (readsA : Reads C i a) (small : a < 12)
    (fixed : Constant ((seedColumns k useHint v).getD a zeroColumn)) :
    Free (prefixColumns (seedColumns k useHint v) (C.gates.take i.val)) (C.gates.get i) := by
  refine Or.inr (Or.inr ⟨a,readsA,?_⟩)
  unfold prefixColumns
  rw [List.getD_append _ _ _ _ (by simpa using small)]
  exact fixed

private theorem missingPrimary (g : Gate) (arity : g.inputs.length ≤ 2) :
    ∃ v : Fin 10, v.val ∉ g.inputs := by
  by_contra! all
  have sub : ({0,1,2} : Finset ℕ) ⊆ g.inputs.toFinset := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    refine List.mem_toFinset.mpr ?_
    rcases hj with rfl | rfl | rfl
    · exact all 0
    · exact all 1
    · exact all 2
  have few := (Finset.card_le_card sub).trans (List.toFinset_card_le (l := g.inputs))
  have three : ({0,1,2} : Finset ℕ).card = 3 := by decide +kernel
  omega

private theorem otherReadAgrees (C : Circuit) (k : Fin 12) (useHint : Bool)
    (h10 : InactiveExtra C k useHint 10) (h11 : InactiveExtra C k useHint 11)
    (p : Fin 10) (x y : Fin 10 → Bool) (agree : ∀ z, z ≠ p → x z = y z)
    (a : ℕ) (lt : a < 12) (other : a ≠ p.val) (used : ReadsInput C a) :
    (seedValues k useHint x).getD a false = (seedValues k useHint y).getD a false := by
  by_cases primary : a < 10
  · let i : Fin 10 := ⟨a,primary⟩
    have no : i ≠ p := fun e => other (congrArg (fun z : Fin 10 => z.val) e)
    exact (inputPrimary k useHint x i).trans ((agree i no).trans (inputPrimary k useHint y i).symm)
  · obtain ⟨b,hb⟩ := fixedExtra C k useHint h10 h11 a (by omega) lt used
    exact (hb x).trans (hb y).symm

theorem noEffectiveExtraFloor (C : Circuit) (k : Fin 12) (useHint : Bool)
    (mono : Monotone2 C) (fits : Fits C k useHint)
    (h10 : InactiveExtra C k useHint 10) (h11 : InactiveExtra C k useHint 11) :
    18 ≤ C.size := by
  have out := fitOutputAtGate C k useHint fits
  let i : GateIndex C := ⟨0,by have hlo := out.1; have hhi := out.2; omega⟩
  let g := C.gates.get i
  have spec : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := monoGate C mono i
  have primaryFree (v : Fin 10) (j : GateIndex C) (read : Reads C j v.val) :
      Free (prefixColumns (seedColumns k useHint v) (C.gates.take j.val)) (C.gates.get j) :=
    freeAtSeedPin C k useHint v j _ read (by have := v.isLt; omega) (constant_literal k useHint v)
  have ready (v : Fin 10) : Ready C k useHint v := by
    intro a limit used
    by_cases inRaw : a < 10
    · let p : Fin 10 := ⟨a,inRaw⟩
      exact seed_literal_available k useHint v p
    · exact Or.inr (Or.inl (fixedSeedColumn k useHint v a
        (fixedExtra C k useHint h10 h11 a (by omega) limit used)))
  have firstFree (all : ∀ v : Fin 10,
      Free (prefixColumns (seedColumns k useHint v) (C.gates.take i.val)) g) :
      18 ≤ C.size := by
    obtain ⟨v,absent⟩ := missingPrimary g spec.2
    obtain ⟨j,hj⟩ := positiveReader C k useHint v mono fits
    have diff : i ≠ j := by
      intro e
      subst j
      exact absent hj
    exact cofactorFloorTwo C k useHint v mono out.1 (ready v) fits i j diff
      (all v) (primaryFree v j hj)
  by_cases twoPrimary : ∃ p q : Fin 10, p ≠ q ∧ g.inputs = [p.val,q.val]
  · obtain ⟨p,q,diff,pins⟩ := twoPrimary
    have readP : Reads C i p.val := by change p.val ∈ g.inputs; simp [pins]
    let controlling := !(g.op.eval [])
    obtain ⟨x,y,_,_,xq,yq,agree,off,on⟩ :=
      Dependence.dependence_at_value p q diff controlling
    have frozen :
        (C.wires (seedValues k useHint x)).getD (12+i.val) false =
        (C.wires (seedValues k useHint y)).getD (12+i.val) false := by
      apply equalAtGateOnInitialPins C k useHint i x y
      · intro t ht
        change t ∈ g.inputs at ht
        simp only [pins,List.mem_cons,List.mem_nil_iff,or_false] at ht
        rcases ht with rfl | rfl
        · exact p.isLt.trans (by decide)
        · exact q.isLt.trans (by decide)
      · change g.op.eval (g.inputs.map (fun t => (seedValues k useHint x).getD t false)) =
          g.op.eval (g.inputs.map (fun t => (seedValues k useHint y).getD t false))
        simp only [pins,List.map_cons,List.map_nil,inputPrimary]
        rcases spec.1 with isAnd | isOr
        · have hx : x q = false := by simpa [controlling,isAnd,GateOp.eval] using xq
          have hy : y q = false := by simpa [controlling,isAnd,GateOp.eval] using yq
          simp [isAnd,GateOp.eval,hx,hy]
        · have hx : x q = true := by simpa [controlling,isOr,GateOp.eval] using xq
          have hy : y q = true := by simpa [controlling,isOr,GateOp.eval] using yq
          simp [isOr,GateOp.eval,hx,hy]
    have second : ∃ j : GateIndex C, j ≠ i ∧ Reads C j p.val := by
      by_contra onlyFirst
      apply impossibleAgreement C k useHint fits x y off on
      intro j
      by_cases isFirst : j = i
      · subst j
        exact Or.inl frozen
      · refine Or.inr fun t read upper => ?_
        have unequal : t ≠ p.val := by
          rintro rfl
          exact onlyFirst ⟨j,isFirst,read⟩
        exact otherReadAgrees C k useHint h10 h11 p x y agree t upper unequal
          ⟨C.gates.get j,List.get_mem _ _,read⟩
    obtain ⟨j,other,readsP⟩ := second
    exact cofactorFloorTwo C k useHint p mono out.1 (ready p) fits i j other.symm
      (primaryFree p i readP) (primaryFree p j readsP)
  · apply firstFree
    intro v
    by_cases short : g.inputs.length ≤ 1
    · exact Or.inl short
    have length : g.inputs.length = 2 := by omega
    obtain ⟨a,b,pins⟩ := List.length_eq_two.mp length
    by_cases same : a = b
    · exact Or.inr (Or.inl ⟨a,by simpa only [same] using pins⟩)
    have high (pin : ℕ) (lower : 10 ≤ pin) (used : pin ∈ g.inputs) :
        Free (prefixColumns (seedColumns k useHint v) (C.gates.take i.val)) g := by
      by_cases below : pin < 12
      · exact freeAtSeedPin C k useHint v i pin used below
          (fixedSeedColumn k useHint v pin
            (fixedExtra C k useHint h10 h11 pin lower below ⟨g,List.get_mem _ _,used⟩))
      · refine Or.inr (Or.inr ⟨pin,used,?_⟩)
        have emptyPrefix : C.gates.take i.val = [] := by simp [i]
        rw [emptyPrefix]
        have value : prefixColumns (seedColumns k useHint v) [] = seedColumns k useHint v := by
          change seedColumns k useHint v ++ [] = seedColumns k useHint v
          simp
        rw [value,List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨false,rfl⟩
    by_cases aRaw : a < 10
    · by_cases bRaw : b < 10
      · exact (twoPrimary ⟨⟨a,aRaw⟩,⟨b,bRaw⟩,fun h =>
          same (congrArg (fun z : Fin 10 => z.val) h),pins⟩).elim
      · exact high b (by omega) (by simp [pins])
    · exact high a (by omega) (by simp [pins])

end PEqualNP.Outside.L_meta_18007.RawCases

namespace PEqualNP.Outside.L_meta_18007.Monotonicity

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem and_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a && b) ≤ (a' && b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem or_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a || b) ≤ (a' || b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem all_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).all id ≤ (l.map f').all id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    exact and_mono _ _ _ _ (h a) ih

theorem any_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).any id ≤ (l.map f').any id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    exact or_mono _ _ _ _ (h a) ih

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp
    omega

def R (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ ∀ i, W.getD i false ≤ W'.getD i false

theorem step_R (W W' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : R W W') : R (step W g) (step W' g) := by
  obtain ⟨hl, hle⟩ := h
  have hv : g.op.eval (g.inputs.map fun i => W.getD i false) ≤
      g.op.eval (g.inputs.map fun i => W'.getD i false) := by
    rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
    · exact all_mono _ _ _ hle
    · exact any_mono _ _ _ hle
  refine ⟨by simp [step, hl], fun i => ?_⟩
  simp only [step, getD_snoc, hl]
  split_ifs
  · exact hle i
  · exact hv
  · exact le_refl _

theorem fold_R (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, R W W' → R (gs.foldl step W) (gs.foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_R W W' g (hgs g List.mem_cons_self) h)

theorem R_append {l1 l1' l2 l2' : List Bool} (h1 : R l1 l1') (h2 : R l2 l2') :
    R (l1 ++ l2) (l1' ++ l2') := by
  obtain ⟨hl1, h1⟩ := h1
  obtain ⟨hl2, h2⟩ := h2
  refine ⟨by simp [hl1, hl2], fun i => ?_⟩
  by_cases hi : i < l1.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl1 ▸ hi)]
    exact h1 i
  · have hi' : l1.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hi', List.getD_append_right _ _ _ _ (hl1 ▸ hi'), hl1]
    exact h2 _

theorem R_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i ≤ g i) :
    R (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, fun i => ?_⟩
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn]
    exact h ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem eval_mono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (l l' : List Bool)
    (h : R l l') : C.eval l ≤ C.eval l' := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  show (C.wires l).getD C.output false ≤ (C.wires l').getD C.output false
  rw [wires_eq, wires_eq]
  exact (fold_R C.gates hops _ _ h).2 C.output

end PEqualNP.Outside.L_meta_18007.Monotonicity

namespace PEqualNP.Outside.L_meta_18007.LowWeight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.Monotonicity (R R_append R_ofFn and_mono eval_mono)
open PEqualNP.Outside.L_meta_18007.NotBudget (target base inputs)

def weight (x : Fin 10 → Bool) : ℕ := (List.ofFn x).count true

private theorem count_ofFn {n : ℕ} (x : Fin n → Bool) :
    (List.ofFn x).count true = (Finset.univ.filter fun i => x i = true).card := by
  have map : List.ofFn x = (List.finRange n).map x := List.ofFn_eq_map
  have univ : (List.finRange n).toFinset = Finset.univ := by
    ext i
    simp
  have count := (List.nodup_finRange n).card_eq_countP (P := fun i => x i = true)
  rw [univ] at count
  have predicates : ((fun a : Bool => a == true) ∘ x) = (fun i => decide (x i = true)) := by
    funext i
    change (x i == true) = decide (x i = true)
    cases x i <;> rfl
  rw [map, List.count_eq_countP, List.countP_map, predicates, ← count]

private def outer (a b c d e : Bool) : Bool :=
  (a && b) || (b && c) || (c && d) || (d && e) || (e && a)

private def inner (a b c d e : Bool) : Bool :=
  (a && c) || (c && e) || (e && b) || (b && d) || (d && a)

private theorem outerCap : ∀ a b c d e : Bool,
    outer a b c d e = false → ([a,b,c,d,e] : List Bool).count true ≤ 2 := by
  decide +kernel

private theorem innerCap : ∀ a b c d e : Bool,
    inner a b c d e = false → ([a,b,c,d,e] : List Bool).count true ≤ 2 := by
  decide +kernel

theorem false_weight_le (x : Fin 10 → Bool) (h : target x = false) : weight x ≤ 4 := by
  have sides : ((outer (x 0) (x 1) (x 2) (x 3) (x 4) ||
      ((x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9))) ||
      inner (x 5) (x 6) (x 7) (x 8) (x 9)) = false := by
    simpa only [outer, inner, target, Bool.or_assoc] using h
  have out := (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp sides).1).1
  have inside := (Bool.or_eq_false_iff.mp sides).2
  have bound₁ := outerCap _ _ _ _ _ out
  have bound₂ := innerCap _ _ _ _ _ inside
  change ([x 0,x 1,x 2,x 3,x 4] ++ [x 5,x 6,x 7,x 8,x 9] : List Bool).count true ≤ 4
  rw [List.count_append]
  omega

private def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)]

private theorem true_edge (x : Fin 10 → Bool) :
    target x = true ↔ ∃ e ∈ edges, x e.1 = true ∧ x e.2 = true := by
  have same : target x = edges.any (fun e => x e.1 && x e.2) := by
    simp [target, edges, Bool.or_assoc]
  rw [same, List.any_eq_true]
  simp only [Bool.and_eq_true]

private def extra (k : Fin 12) : Finset (Fin 10) :=
  if hk : k.val < 10 then {⟨k.val,hk⟩} else if k.val = 10 then {0,2} else ∅

private def keepSet (e : Fin 10 × Fin 10) (k : Fin 12) : Finset (Fin 10) :=
  {e.1,e.2} ∪ extra k

private def keep (e : Fin 10 × Fin 10) (k : Fin 12) (x : Fin 10 → Bool) :
    Fin 10 → Bool := fun i => x i && decide (i ∈ keepSet e k)

private theorem keep_le (e : Fin 10 × Fin 10) (k : Fin 12) (x : Fin 10 → Bool) :
    ∀ i, keep e k x i ≤ x i := by
  intro i
  cases h : x i <;> simp [keep,h]

private theorem keep_weight (e : Fin 10 × Fin 10) (k : Fin 12) (x : Fin 10 → Bool) :
    weight (keep e k x) ≤ 4 := by
  unfold weight
  rw [count_ofFn]
  have below : (Finset.univ.filter fun i => keep e k x i = true) ⊆ keepSet e k := by
    intro i hm
    have one := (Finset.mem_filter.mp hm).2
    change (x i && decide (i ∈ keepSet e k)) = true at one
    simp only [Bool.and_eq_true, decide_eq_true_eq] at one
    exact one.2
  have edgeCap : ({e.1,e.2} : Finset (Fin 10)).card ≤ 2 := by
    simpa using (Finset.card_insert_le e.1 ({e.2} : Finset (Fin 10)))
  have extraCap : (extra k).card ≤ 2 := by
    unfold extra
    split_ifs <;> simp
  have total := Finset.card_union_le ({e.1,e.2} : Finset (Fin 10)) (extra k)
  have sub := Finset.card_le_card below
  change _ ≤ ({e.1,e.2} ∪ extra k : Finset (Fin 10)).card at sub
  omega

private theorem keep_target (e : Fin 10 × Fin 10) (k : Fin 12) (x : Fin 10 → Bool)
    (he : e ∈ edges) (ha : x e.1 = true) (hb : x e.2 = true) :
    target (keep e k x) = true := by
  apply (true_edge _).mpr
  exact ⟨e,he,by simp [keep, keepSet, ha],by simp [keep, keepSet, hb]⟩

private theorem base_primary (x : Fin 10 → Bool) (i : Fin 10) :
    (base x).getD i.val false = x i := by
  unfold base
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt),
    List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn] <;> rfl

private theorem base_hint (x : Fin 10 → Bool) :
    (base x).getD 10 false = (x 0 && x 2) := by
  unfold base
  rw [List.getD_append_right _ _ _ _ (by simp)] <;> simp

private theorem base_outside (x : Fin 10 → Bool) (i : ℕ) (hi : 11 ≤ i) :
    (base x).getD i false = false := by
  exact List.getD_eq_default _ _ (by simpa [base] using hi)

private theorem keep_seed (e : Fin 10 × Fin 10) (k : Fin 12) (x : Fin 10 → Bool) :
    (base (keep e k x)).getD k.val false = (base x).getD k.val false := by
  by_cases hk : k.val < 10
  · let i : Fin 10 := ⟨k.val,hk⟩
    change (base (keep e k x)).getD i.val false = (base x).getD i.val false
    rw [base_primary, base_primary]
    have atI : i ∈ keepSet e k := by simp [keepSet, extra, hk, i]
    simp [keep, atI]
  · by_cases h10 : k.val = 10
    · rw [h10, base_hint, base_hint]
      have h₀ : (0 : Fin 10) ∈ keepSet e k := by simp [keepSet, extra, hk, h10]
      have h₂ : (2 : Fin 10) ∈ keepSet e k := by simp [keepSet, extra, hk, h10]
      simp [keep,h₀,h₂]
    · rw [base_outside _ _ (by omega), base_outside _ _ (by omega)]

private theorem R_singleton {a b : Bool} (h : a ≤ b) : R [a] [b] := by
  refine ⟨rfl, ?_⟩
  intro i
  cases i with
  | zero => exact h
  | succ i =>
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp)] <;> exact le_refl _

private def withHint (k : Fin 12) (x : Fin 10 → Bool) (hint : Bool) : List Bool :=
  (List.ofFn x ++ [hint]) ++ [!(base x).getD k.val false]

private theorem withHint_mono (k : Fin 12) (y x : Fin 10 → Bool) (ha hb : Bool)
    (hy : ∀ i, y i ≤ x i) (hh : ha ≤ hb)
    (seed : (base y).getD k.val false = (base x).getD k.val false) :
    R (withHint k y ha) (withHint k x hb) :=
  R_append (R_append (R_ofFn y x hy) (R_singleton hh))
    (R_singleton (by rw [seed] <;> exact le_refl _))

theorem full_of_weight_four (C : Circuit) (k : Fin 12) (mono : Monotone2 C)
    (fits : ∀ x, weight x ≤ 4 → C.eval (inputs k x) = target x) :
    ∀ x, C.eval (inputs k x) = target x := by
  intro x
  cases h : target x with
  | false => exact (fits x (false_weight_le x h)).trans h
  | true =>
      obtain ⟨e,he,ha,hb⟩ := (true_edge x).mp h
      let y := keep e k x
      have yTrue : target y = true := keep_target e k x he ha hb
      have yFit := (fits y (keep_weight e k x)).trans yTrue
      have yLe : ∀ i, y i ≤ x i := keep_le e k x
      have relation : R (inputs k y) (inputs k x) :=
        withHint_mono k y x _ _ yLe (and_mono _ _ _ _ (yLe 0) (yLe 2)) (keep_seed e k x)
      have monotone := eval_mono C mono _ _ relation
      rw [yFit] at monotone
      exact Bool.eq_true_of_true_le monotone

def Exceptional (k : Fin 12) : Prop := k.val = 0 ∨ k.val = 2 ∨ k.val = 10

def noHintInputs (k : Fin 12) (x : Fin 10 → Bool) : List Bool :=
  withHint k x false

private theorem edge_not_hint : ∀ e : Fin 10 × Fin 10, e ∈ edges →
    ¬ ((0 : Fin 10) ∈ ({e.1,e.2} : Finset (Fin 10)) ∧
      (2 : Fin 10) ∈ ({e.1,e.2} : Finset (Fin 10))) := by
  decide +kernel

private theorem extra_not_hint (k : Fin 12) (ordinary : ¬Exceptional k) :
    (0 : Fin 10) ∉ extra k ∧ (2 : Fin 10) ∉ extra k := by
  have h₀ : k.val ≠ 0 := fun h => ordinary (Or.inl h)
  have h₂ : k.val ≠ 2 := fun h => ordinary (Or.inr (Or.inl h))
  have h₁₀ : k.val ≠ 10 := fun h => ordinary (Or.inr (Or.inr h))
  by_cases hk : k.val < 10
  · have zero : (0 : Fin 10) ≠ ⟨k.val,hk⟩ := by
      intro h
      exact h₀ (congrArg Fin.val h).symm
    have two : (2 : Fin 10) ≠ ⟨k.val,hk⟩ := by
      intro h
      exact h₂ (congrArg Fin.val h).symm
    simp [extra,hk,zero,two]
  · simp [extra,hk,h₁₀]

private theorem keep_hint_false (e : Fin 10 × Fin 10) (he : e ∈ edges) (k : Fin 12)
    (ordinary : ¬Exceptional k) (x : Fin 10 → Bool) :
    (keep e k x 0 && keep e k x 2) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h₀,h₂⟩ := h
  change (x 0 && decide ((0 : Fin 10) ∈ keepSet e k)) = true at h₀
  change (x 2 && decide ((2 : Fin 10) ∈ keepSet e k)) = true at h₂
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h₀ h₂
  have zero := h₀.2
  have two := h₂.2
  have blocked := extra_not_hint k ordinary
  exact edge_not_hint e he
    ⟨(Finset.mem_union.mp zero).resolve_right blocked.1,
      (Finset.mem_union.mp two).resolve_right blocked.2⟩

theorem full_without_hint (C : Circuit) (k : Fin 12) (mono : Monotone2 C)
    (ordinary : ¬Exceptional k) (fits : ∀ x, C.eval (inputs k x) = target x) :
    ∀ x, C.eval (noHintInputs k x) = target x := by
  intro x
  cases h : target x with
  | false =>
      have relation : R (noHintInputs k x) (inputs k x) :=
        withHint_mono k x x false _ (fun _ => le_refl _) (Bool.false_le _) rfl
      have order := eval_mono C mono _ _ relation
      rw [fits x,h] at order
      exact le_antisymm order (Bool.false_le _)
  | true =>
      obtain ⟨e,he,ha,hb⟩ := (true_edge x).mp h
      let y := keep e k x
      have same : noHintInputs k y = inputs k y := by
        change withHint k y false = withHint k y (y 0 && y 2)
        rw [keep_hint_false e he k ordinary x]
      have yFit : C.eval (noHintInputs k y) = true :=
        (congrArg C.eval same).trans ((fits y).trans (keep_target e k x he ha hb))
      have relation : R (noHintInputs k y) (noHintInputs k x) :=
        withHint_mono k y x false false (keep_le e k x) (le_refl _) (keep_seed e k x)
      have order := eval_mono C mono _ _ relation
      rw [yFit] at order
      exact Bool.eq_true_of_true_le order

def ExceptionalCase : Prop :=
  ∀ (C : Circuit) (k : Fin 12), Exceptional k → Monotone2 C → C.size ≤ 17 →
    ∃ x, C.eval (inputs k x) ≠ target x

def OrdinaryCase : Prop :=
  ∀ (C : Circuit) (k : Fin 12), ¬Exceptional k → Monotone2 C → C.size ≤ 17 →
    ∃ x, C.eval (noHintInputs k x) ≠ target x

theorem weight_four_of_cases (exceptional : ExceptionalCase) (ordinary : OrdinaryCase)
    (C : Circuit) (k : Fin 12) (fan : FanInTwo C)
    (pure : ∀ g ∈ C.gates, g.op ≠ GateOp.not) (size : C.size ≤ 17) :
    ∃ x, weight x ≤ 4 ∧ C.eval (inputs k x) ≠ target x := by
  by_contra missing
  have mono : Monotone2 C := by
    intro g hg
    have ops : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan g hg).1
    have allowed : g.op = GateOp.and ∨ g.op = GateOp.or := by
      rcases ops with a | b | c
      · exact Or.inl a
      · exact Or.inr b
      · exact (pure g hg c).elim
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using allowed,(fan g hg).2⟩
  have fits (x : Fin 10 → Bool) (w : weight x ≤ 4) : C.eval (inputs k x) = target x := by
    by_contra differs
    exact missing ⟨x,w,differs⟩
  have full := full_of_weight_four C k mono fits
  by_cases hk : Exceptional k
  · obtain ⟨x,hx⟩ := exceptional C k hk mono size
    exact hx (full x)
  · obtain ⟨x,hx⟩ := ordinary C k hk mono size
    exact hx (full_without_hint C k mono hk full x)

end PEqualNP.Outside.L_meta_18007.LowWeight

namespace PEqualNP.Outside.L_meta_18007.RawCofactor

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_18007.NineInputs (Wire Constant Row)

private theorem prefixRetainsRead {R : Type} (seed : List (Wire R))
    (gs : List Gate) (count pin : ℕ)
    (earlier : pin < (prefixColumns seed (gs.take count)).length) :
    (prefixColumns seed (gs.take count)).getD pin zeroColumn =
      (prefixColumns seed gs).getD pin zeroColumn := by
  let prior := afterColumns seed (gs.take count) []
  obtain ⟨tail, ext, _⟩ := afterColumns_extends seed prior (gs.drop count)
  have eq : prefixColumns seed gs = prefixColumns seed (gs.take count) ++ tail := by
    unfold prefixColumns
    conv_lhs => rw [← List.take_append_drop count gs, afterColumns_append]
    change seed ++ afterColumns seed (gs.drop count) prior = (seed ++ prior) ++ tail
    rw [ext, List.append_assoc]
  rw [eq,List.getD_append _ _ _ _ earlier]

theorem consumerIsFree (C : Circuit) (k : Fin 12) (v : Fin 10)
    (i j : Fin C.gates.length) (ordered : i.val < j.val)
    (aliasesPrimary : ∀ x, (C.wires (seedValues k true x)).getD (12 + i.val) false = x v)
    (reads : 12 + i.val ∈ (C.gates.get j).inputs) :
    Free (prefixColumns (seedColumns k true v) (C.gates.take j.val)) (C.gates.get j) := by
  let seed := seedColumns k true v
  have earlier : 12 + i.val < (prefixColumns seed (C.gates.take j.val)).length := by
    rw [prefix_length, show seed.length = 12 from seedColumns_length k true v, List.length_take]
    rw [Nat.min_eq_left j.isLt.le]
    omega
  refine .inr (.inr ⟨12 + i.val, reads, false, ?_⟩)
  change (prefixColumns seed (C.gates.take j.val)).getD (12 + i.val) zeroColumn = fun _ => false
  rw [prefixRetainsRead _ _ _ _ earlier]
  funext r
  have value := List.getD_map (l := prefixColumns seed C.gates) (n := 12 + i.val)
    (d := zeroColumn) (fun f : Wire Row => f r)
  rw [prefix_at, seedColumns_at] at value
  rw [← value]
  change (C.wires (seedValues k true (restrictedAll v r))).getD (12 + i.val) false = false
  exact (aliasesPrimary _).trans (restrictedAll_self v r)

end PEqualNP.Outside.L_meta_18007.RawCofactor

namespace PEqualNP.Outside.L_meta_18007.RawCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.RawCofactor

theorem indexedReader (C : Circuit) (a : ℕ) :
    ReadsInput C a ↔ ∃ i : GateIndex C, Reads C i a := by
  constructor
  · rintro ⟨g,mem,read⟩
    obtain ⟨i,eq⟩ := List.mem_iff_get.mp mem
    refine ⟨i,?_⟩
    change a ∈ (C.gates.get i).inputs
    rwa [eq]
  · rintro ⟨i,reads⟩
    exact ⟨C.gates.get i, List.get_mem C.gates i, reads⟩

theorem boundaryFloor (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (hintFixed : useHint = false ∨ v = 0 ∨ v = 2)
    (negativeFixed : k.val = v.val ∨ k.val = 11 ∨ (k.val = 10 ∧ (v = 0 ∨ v = 2)))
    (mono : Monotone2 C) (fits : Fits C k useHint)
    (i j : GateIndex C) (distinct : i ≠ j)
    (hi : ReadsOneOf C i {v.val,10,11}) (hj : ReadsOneOf C j {v.val,10,11}) :
    18 ≤ C.size := by
  have free (g : GateIndex C) (h : ReadsOneOf C g {v.val,10,11}) :
      Free (prefixColumns (seedColumns k useHint v) (C.gates.take g.val)) (C.gates.get g) := by
    obtain ⟨pin,member,reads⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    apply freeAtSeedPin C k useHint v g pin reads
    · rcases member with rfl | rfl | rfl
      · have := v.isLt
        omega
      · decide
      · decide
    · rcases member with rfl | rfl | rfl
      · exact constant_literal _ _ _
      · exact constant_hint _ _ _ hintFixed
      · exact constant_neg _ _ _ negativeFixed
  exact cofactorFloorTwo C k useHint v mono (fitOutputAtGate C k useHint fits).1
    (seed_ready C k useHint v (.inl hintFixed) (.inl negativeFixed)) fits
    i j distinct (free i hi) (free j hj)

end PEqualNP.Outside.L_meta_18007.RawCases

namespace PEqualNP.Outside.L_meta_18007.RawCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_18007.NotBudget (target)
open PEqualNP.Outside.L_meta_18007.RawCofactor

private theorem inactiveFalseHint (C : Circuit) (k : Fin 12) :
    InactiveExtra C k false 10 :=
  .inl ⟨false, fun x => by rw [inputHint]; rfl⟩

private theorem literalSeedFloor (C : Circuit) (k : Fin 12) (useHint : Bool) (v : Fin 10)
    (index : k.val = v.val) (hintFixed : useHint = false ∨ v = 0 ∨ v = 2)
    (mono : Monotone2 C) (fits : Fits C k useHint) : 18 ≤ C.size := by
  classical
  by_cases used : ReadsInput C 11 ∨ (useHint = true ∧ ReadsInput C 10)
  · obtain ⟨i,hi⟩ := positiveReader C k useHint v mono fits
    have inPins : ReadsOneOf C i {v.val,10,11} := ⟨v.val, by simp, hi⟩
    rcases twoReadersOrUnique C _ i inPins with ⟨j,ne,hj⟩ | unique
    · exact boundaryFloor C k useHint v hintFixed (.inl index) mono fits i j ne.symm inPins hj
    · have untouched (j : GateIndex C) (ne : j ≠ i) : ¬ ReadsOneOf C j {v.val,10,11} :=
        fun h => ne (unique j h)
      rcases used with negative | ⟨hintOn, positive⟩
      · obtain ⟨j,hj⟩ := (indexedReader C 11).mp negative
        have eq := unique j ⟨11,by simp,hj⟩
        subst j
        have pins := connectsExactly (monoGate C mono i).2 hi hj (by have := v.isLt; omega)
        exact (onlyComplementReaderImpossible C k useHint v index mono fits i untouched pins).elim
      · subst useHint
        have endpoint : v = 0 ∨ v = 2 := hintFixed.resolve_left (by decide)
        obtain ⟨j,hj⟩ := (indexedReader C 10).mp positive
        have eq := unique j ⟨10,by simp,hj⟩
        subst j
        have pins := connectsExactly (monoGate C mono i).2 hi hj (by have := v.isLt; omega)
        obtain ⟨wire, q, order, reads⟩ := endpointHintAlias C k v i endpoint pins untouched mono fits
        have v12 : v.val < 12 := by have := v.isLt; omega
        exact cofactorFloorTwo C k true v mono (fitOutputAtGate C k true fits).1
          (seed_ready C k true v (.inl (.inr endpoint)) (.inl (.inl index))) fits
          i q (fun eq => (Nat.ne_of_lt order) (congrArg Fin.val eq))
          (freeAtSeedPin C k true v i v.val hi v12 (constant_literal _ _ _))
          (consumerIsFree C k v i q order wire reads)
  · have h10 : InactiveExtra C k useHint 10 := by
      cases useHint
      · exact inactiveFalseHint C k
      · exact .inr (fun h => used (.inr ⟨rfl,h⟩))
    exact noEffectiveExtraFloor C k useHint mono fits h10 (.inr (fun h => used (.inl h)))

private theorem hintSeedFloor (C : Circuit) (mono : Monotone2 C) (fits : Fits C 10 true) :
    18 ≤ C.size := by
  classical
  by_cases extras : ReadsInput C 10 ∨ ReadsInput C 11
  · obtain ⟨pin, hp, use⟩ : ∃ a : ℕ, (a = 10 ∨ a = 11) ∧ ReadsInput C a := by
      rcases extras with h | h
      · exact ⟨10,.inl rfl,h⟩
      · exact ⟨11,.inr rfl,h⟩
    obtain ⟨i,read⟩ := (indexedReader C pin).mp use
    obtain ⟨u,ru⟩ := positiveReader C 10 true 0 mono fits
    obtain ⟨w,rw⟩ := positiveReader C 10 true 2 mono fits
    have lower (v : Fin 10) (endpoint : v = 0 ∨ v = 2)
        (j : GateIndex C) (rj : Reads C j v.val) (ne : j ≠ i) : 18 ≤ C.size := by
      apply boundaryFloor C 10 true v (.inr endpoint) (.inr (.inr ⟨rfl,endpoint⟩))
        mono fits j i ne
      · exact ⟨v.val, by simp, rj⟩
      · exact ⟨pin, by simp [hp],read⟩
    by_cases hu : u = i
    · by_cases hw : w = i
      · subst u
        subst w
        have form := connectsExactly (monoGate C mono i).2 ru rw (by decide)
        have bad : pin = 0 ∨ pin = 2 := by
          change pin ∈ (C.gates.get i).inputs at read
          rcases form with h | h
          · rw [h] at read
            simpa using read
          · rw [h] at read
            simpa [or_comm] using read
        rcases hp with rfl | rfl <;> simp at bad
      · exact lower 2 (.inr rfl) w rw hw
    · exact lower 0 (.inl rfl) u ru hu
  · exact noEffectiveExtraFloor C 10 true mono fits
      (.inr (fun h => extras (.inl h))) (.inr (fun h => extras (.inr h)))

theorem exceptionalImpossible : LowWeight.ExceptionalCase := by
  intro C k exceptional mono cap
  by_contra missing
  have fits : Fits C k true := by
    intro x
    by_contra differs
    exact missing ⟨x,differs⟩
  have lower : 18 ≤ C.size := by
    rcases exceptional with first | second | both
    · exact literalSeedFloor C k true 0 first (.inr (.inl rfl)) mono fits
    · exact literalSeedFloor C k true 2 second (.inr (.inr rfl)) mono fits
    · have eq : k = 10 := Fin.ext both
      subst k
      exact hintSeedFloor C mono fits
  omega

theorem ordinaryImpossible : LowWeight.OrdinaryCase := by
  intro C k ordinary mono cap
  by_contra missing
  have fits : Fits C k false := by
    intro x
    by_contra differs
    exact missing ⟨x,differs⟩
  have lower : 18 ≤ C.size := by
    by_cases small : k.val < 10
    · exact literalSeedFloor C k false ⟨k.val,small⟩ rfl (.inl rfl) mono fits
    · rcases nonprimarySeedCases k small with rfl | rfl
      · exact (ordinary (.inr (.inr rfl))).elim
      · exact noEffectiveExtraFloor C 11 false mono fits (inactiveFalseHint C 11)
          (.inl ⟨true, negatedMissing false⟩)
  omega

end PEqualNP.Outside.L_meta_18007.RawCases

theorem PEqualNP.Outside.L_meta_18007 :
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ x4 ∈ x1.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →       x1.size ≤ (17 : ℕ) →         ∃ (x6 : Fin (10 : ℕ) → Bool),           List.count Bool.true (List.ofFn x6) ≤ (4 : ℕ) ∧             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))];             have x8 : List Bool := x7 ++ [!x7.getD (↑x2) Bool.false];             x1.eval x8 ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)))) := by
  exact PEqualNP.Outside.L_meta_18007.LowWeight.weight_four_of_cases
    PEqualNP.Outside.L_meta_18007.RawCases.exceptionalImpossible PEqualNP.Outside.L_meta_18007.RawCases.ordinaryImpossible
