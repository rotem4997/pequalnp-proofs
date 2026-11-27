import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5479

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def free (m : ℕ) (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = m ∨ v ∈ S

def comb (m : ℕ) (o : Fin 3) (a b : ℕ) : ℕ :=
  if o = 0 then a &&& b else if o = 1 then a ||| b else m ^^^ a

def Can (m f : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => free m S f
  | k+1, S => ∃ (o : Fin 3) (a b : ℕ), free m S a ∧ free m S b ∧ Can m f k (insert (comb m o a b) S)

theorem freeMono {m v : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hv : free m S v) : free m T v :=
  hv.imp_right (Or.imp_right (fun e => h e))

theorem monoC {m f k : ℕ} {S T : Finset ℕ} (h : S ⊆ T) (hc : Can m f k S) : Can m f k T := by
  induction k generalizing S T with
  | zero => exact freeMono h hc
  | succ k ih =>
    obtain ⟨o,a,b,ha,hb,hh⟩ := hc
    exact ⟨o,a,b,freeMono h ha,freeMono h hb,ih (Finset.insert_subset_insert _ h) hh⟩

theorem stepUp {m f k : ℕ} {S : Finset ℕ} (hc : Can m f k S) : Can m f (k+1) S :=
  ⟨0,0,0,Or.inl rfl,Or.inl rfl,monoC (Finset.subset_insert _ _) hc⟩

theorem small {m f k : ℕ} {S : Finset ℕ} (hc : Can m f k S) :
    ∃ T ⊆ S, T.card ≤ k+1 ∧ Can m f k T := by
  induction k generalizing S with
  | zero =>
    rcases hc with h | h | h
    · exact ⟨∅,by simp,by simp,Or.inl h⟩
    · exact ⟨∅,by simp,by simp,Or.inr (Or.inl h)⟩
    · exact ⟨{f},by simpa,by simp,Or.inr (Or.inr (by simp))⟩
  | succ k ih =>
    obtain ⟨o,a,b,ha,hb,hh⟩ := hc
    let v := comb m o a b
    obtain ⟨T,hT,hn,hc'⟩ := ih hh
    change T ⊆ insert v S at hT
    by_cases hv : v ∈ T
    · let U := T.erase v ∪ ({a,b} ∩ S)
      have hu : T.erase v ⊆ S := by
        intro x hx
        exact (Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx))).resolve_left (Finset.ne_of_mem_erase hx)
      have hU : U ⊆ S := Finset.union_subset hu Finset.inter_subset_right
      have liftWire : ∀ w ∈ ({a,b} : Finset ℕ), free m S w → free m U w := by
        intro w hw he
        exact he.imp_right (Or.imp_right (fun h => Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hw,h⟩)))
      have hcard := Finset.card_union_le (T.erase v) ({a,b} ∩ S)
      have hpair := Finset.card_le_card (Finset.inter_subset_left : ({a,b} ∩ S) ⊆ {a,b})
      have htwo : ({a,b} : Finset ℕ).card ≤ 2 := by
        calc
          _ ≤ ({b} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
          _ = _ := by simp
      rw [Finset.card_erase_of_mem hv] at hcard
      refine ⟨U,hU,by dsimp [U]; omega,o,a,b,liftWire a (by simp) ha,liftWire b (by simp) hb,monoC ?_ hc'⟩
      intro x hx
      by_cases e : x = v
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hx⟩)))
    · refine ⟨T,?_,by omega,stepUp hc'⟩
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun e => hv (e ▸ hx))

theorem agreeC {m f k p q : ℕ} {S : Finset ℕ} (hc : Can m f k S)
    (hm : m.testBit p = m.testBit q) (hs : ∀ v ∈ S, Nat.testBit v p = Nat.testBit v q) :
    f.testBit p = f.testBit q := by
  have w {v} (hv : free m S v) : Nat.testBit v p = Nat.testBit v q := by
    rcases hv with rfl | rfl | h
    · simp
    · exact hm
    · exact hs _ h
  induction k generalizing S with
  | zero => exact w hc
  | succ k ih =>
    obtain ⟨o,a,b,ha,hb,hh⟩ := hc
    have hg : (comb m o a b).testBit p = (comb m o a b).testBit q := by
      unfold comb
      fin_cases o <;> simp [Nat.testBit_xor,w ha,w hb,hm]
    apply ih hh
    all_goals first
      | intro v hv; rcases Finset.mem_insert.mp hv with rfl | h; exact hg; exact hs _ h
      | intro v hv; rcases hv with rfl | rfl | h; simp; exact hm; rcases Finset.mem_insert.mp h with rfl | h; exact hg; exact hs _ h

def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0


def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]


def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0


def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, hM]

theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]


theorem wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))


theorem getWire (T : List ℕ) (i : ℕ) (m : ℕ) : free m T.toFinset (T.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T[i]? with
  | none => exact Or.inl rfl
  | some t => exact Or.inr (Or.inr (List.mem_toFinset.mpr (List.mem_of_getElem? h)))

theorem gateChoice (m : ℕ) (T : List ℕ) (g : Gate) (hg : GOk g) :
    ∃ (o : Fin 3) (a b : ℕ), free m T.toFinset a ∧ free m T.toFinset b ∧
      gt m g.op (g.inputs.map fun i => T.getD i 0) = comb m o a b := by
  obtain ⟨hop,hl⟩ := hg
  generalize g.inputs = ins at hl ⊢
  have z : free m T.toFinset 0 := Or.inl rfl
  have u : free m T.toFinset m := Or.inr (Or.inl rfl)
  match ins, hl with
  | [], _ =>
    rcases hop with h | h | h <;> rw [h]
    · exact ⟨1,m,0,u,z,by simp [gt,comb]⟩
    · exact ⟨1,0,0,z,z,rfl⟩
    · exact ⟨1,m,0,u,z,by simp [gt,comb]⟩
  | [i], _ =>
    rcases hop with h | h | h <;> rw [h]
    · exact ⟨1,_,0,getWire T i m,z,by simp [gt,comb]⟩
    · exact ⟨1,_,0,getWire T i m,z,by simp [gt,comb]⟩
    · exact ⟨2,_,0,getWire T i m,z,rfl⟩
  | [i,j], _ =>
    rcases hop with h | h | h <;> rw [h]
    · exact ⟨0,_,_,getWire T i m,getWire T j m,rfl⟩
    · exact ⟨1,_,_,getWire T i m,getWire T j m,rfl⟩
    · exact ⟨2,_,_,getWire T i m,getWire T j m,rfl⟩

theorem fromTabs (m f : ℕ) (gs : List Gate) (T : List ℕ) (ok : ∀ g ∈ gs, GOk g)
    (h : free m (tabs m T gs).toFinset f) : Can m f gs.length T.toFinset := by
  induction gs generalizing T with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨o,a,b,ha,hb,e⟩ := gateChoice m T g (ok g (by simp))
    have hh := ih (tstep m T g) (fun g' hg' => ok _ (by simp [hg'])) h
    refine ⟨o,a,b,ha,hb,?_⟩
    rw [← e]
    simpa [tstep] using hh

def cuts : ℕ → List ℕ → List (List ℕ)
  | _, [] => [[]]
  | k, x :: xs => if (x :: xs).length ≤ k then [x :: xs] else
      match k with
      | 0 => [[]]
      | j+1 => (cuts j xs).map (x :: ·) ++ cuts (j+1) xs
termination_by _ l => l.length

theorem cutsSpec (k : ℕ) (l : List ℕ) (T : Finset ℕ) (h : T ⊆ l.toFinset) (n : T.card ≤ k) :
    ∃ U ∈ cuts k l, T ⊆ U.toFinset := by
  induction l generalizing k T with
  | nil => exact ⟨[],by simp [cuts],h⟩
  | cons x xs ih =>
    cases k with
    | zero =>
      have he : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[],by simp [cuts],by simp [he]⟩
    | succ j =>
      rw [cuts]
      split
      · exact ⟨_,by simp,h⟩
      ·
        by_cases hx : x ∈ T
        · have hs : T.erase x ⊆ xs.toFinset := by
            intro y hy
            have hh := h (Finset.mem_of_mem_erase hy)
            simpa [Finset.ne_of_mem_erase hy] using hh
          obtain ⟨U,hU,sub⟩ := ih j (T.erase x) hs (by rw [Finset.card_erase_of_mem hx]; omega)
          refine ⟨x::U,List.mem_append_left _ (List.mem_map.mpr ⟨U,hU,rfl⟩),?_⟩
          intro y hy
          by_cases e : y = x
          · simp [e]
          · simpa [e] using sub (Finset.mem_erase.mpr ⟨e,hy⟩)
        · have hs : T ⊆ xs.toFinset := by
            intro y hy
            have e : y ≠ x := fun he => hx (he ▸ hy)
            simpa [e] using h hy
          obtain ⟨U,hU,sub⟩ := ih (j+1) T hs n
          exact ⟨U,List.mem_append_right _ hU,sub⟩

def mask (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (v ^^^ (v >>> d)) ||| mask d vs

theorem maskFalse {d i : ℕ} {l : List ℕ} (h : (mask d l).testBit i = false) :
    ∀ v ∈ l, Nat.testBit v i = Nat.testBit v (d+i) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [mask,Nat.testBit_lor,Nat.testBit_xor,Nat.testBit_shiftRight,Bool.or_eq_false_iff] at h
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · have hh := h.1
      revert hh
      cases v.testBit i <;> cases v.testBit (d+i) <;> decide
    · exact ih h.2 v hv

theorem covered {m f k d : ℕ} {l : List ℕ} (hc : Can m f k l.toFinset)
    (hp : ∀ i < d, m.testBit i = m.testBit (d+i) ∧ f.testBit i ≠ f.testBit (d+i)) :
    mask d l &&& (2^d-1) = 2^d-1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < d
  · have hh : (mask d l).testBit i = true := by
      cases e : (mask d l).testBit i with
      | true => rfl
      | false =>
        exact False.elim ((hp i h).2 (agreeC hc (hp i h).1 (fun v hv => maskFalse e v (List.mem_toFinset.mp hv))))
    simp [h,hh]
  · simp [h]

def vals (m : ℕ) (S : List ℕ) : List ℕ :=
  let w := 0 :: m :: S
  ((w.flatMap fun a => w.map fun b => a &&& b) ++
   (w.flatMap fun a => w.map fun b => a ||| b) ++ w.map (m ^^^ ·)).eraseDups

theorem memVals {m a b : ℕ} {S : List ℕ} (o : Fin 3) (ha : free m S.toFinset a)
    (hb : free m S.toFinset b) : comb m o a b ∈ vals m S := by
  have toMem {w} (h : free m S.toFinset w) : w ∈ 0 :: m :: S := by simpa [free] using h
  have ha' := toMem ha
  have hb' := toMem hb
  simp only [vals,List.mem_eraseDups,List.mem_append,List.mem_flatMap,List.mem_map]
  fin_cases o
  · exact Or.inl (Or.inl ⟨a,ha',b,hb',rfl⟩)
  · exact Or.inl (Or.inr ⟨a,ha',b,hb',rfl⟩)
  · exact Or.inr ⟨a,ha',rfl⟩

def verify (d m k : ℕ) (S : List ℕ) (nextLevel : List (List ℕ)) : Bool :=
  (vals m S).all fun v =>
    (cuts (k+1) (if v ∈ S then S else v::S)).all fun U =>
      (mask d U &&& (2^d-1) != 2^d-1) || nextLevel.any (fun V => U.all (fun x => V.contains x))

theorem advance {d m f k : ℕ} {S : List ℕ} {N : List (List ℕ)}
    (hp : ∀ i < d, m.testBit i = m.testBit (d+i) ∧ f.testBit i ≠ f.testBit (d+i))
    (hv : verify d m k S N = true) (hc : Can m f (k+1) S.toFinset) :
    ∃ V ∈ N, Can m f k V.toFinset := by
  obtain ⟨o,a,b,ha,hb,hh⟩ := hc
  let v := comb m o a b
  have hg := List.all_eq_true.mp hv v (memVals o ha hb)
  let l := if v ∈ S then S else v::S
  have eqn : l.toFinset = insert v S.toFinset := by
    dsimp [l]
    split
    · rename_i h
      simp [Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)]
    · simp
  obtain ⟨T,hT,hn,ht⟩ := small hh
  obtain ⟨U,hU,hu⟩ := cutsSpec (k+1) l T (eqn ▸ hT) hn
  have hcU := monoC hu ht
  have htest := List.all_eq_true.mp hg U hU
  have hcov := covered hcU hp
  simp only [hcov,bne_self_eq_false,Bool.false_or,List.any_eq_true] at htest
  obtain ⟨V,hV,hsub⟩ := htest
  refine ⟨V,hV,monoC ?_ hcU⟩
  intro x hx
  exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp hsub _ (List.mem_toFinset.mp hx)))


abbrev width : ℕ := 23
abbrev topMask : ℕ := 70368744177663
abbrev targetBits : ℕ := 8388607
def inputs : List ℕ := [18314321719503, 46190382812979, 4467102330940, 280247714752, 18124768345088, 51677054828544]
def row2 : List (List ℕ) := [
]
def row3 : List (List ℕ) := [
  [18314321719503, 46190382812979, 4747352339452, 18124768345088],
  [18314321719503, 46190382812979, 4747354243068, 51677054828544],
  [18314321719503, 46190382812979, 22528520945660, 52026356528124],
  [18314321719503, 46190385106739, 4747350045692, 18124768345088],
  [46190382812979, 18314325916879, 4747350045692, 51677054828544]]
def row4 : List (List ℕ) := [
  [18691689349119, 18314321719503, 46190382812979, 4747350045692, 18124768345088],
  [52243975832575, 18314321719503, 46190382812979, 4747350045692, 51677054828544],
  [65621394131971, 18314321719503, 46190382812979, 18124768345088, 51677054828544],
  [24178361364684, 18314321719503, 4747350045692, 18124768345088, 51677054828544],
  [52054422458160, 46190382812979, 4747350045692, 18124768345088, 51677054828544],
  [2293760, 18314321719503, 46190382812979, 4747350045692, 18124768345088],
  [18314321719503, 4197376, 46190382812979, 4747350045692, 51677054828544],
  [18314321719503, 46190382812979, 4467102330940, 280250008512, 18124768345088],
  [18314321719503, 46190382812979, 4467102330940, 280251912128, 51677054828544],
  [18314321719503, 46190382812979, 4467102330940, 18130138103744, 51957301494720],
  [18314321719503, 46190382812979, 4467104624700, 280247714752, 18124768345088],
  [18314321719503, 46190382812979, 4467106528316, 280247714752, 51677054828544],
  [18314321719503, 46190382812979, 280247714752, 22523151187004, 51746109861948],
  [18314321719503, 46190382812979, 4747350045692, 18124768345088, 51677054828544],
  [18314321719503, 46190382812979, 4747350045692, 18124768345088, 51687943245619],
  [18314321719503, 46190382812979, 4747350045692, 18124768345088, 51746109861948],
  [18314321719503, 46190382812979, 4747350045692, 18124768345088, 51957301494720],
  [18314321719503, 46190382812979, 4747350045692, 18124768345088, 52026356528124],
  [18314321719503, 46190382812979, 4747350045692, 18675103169743, 51677054828544],
  [18314321719503, 46190382812979, 4747350045692, 22523151187004, 51677054828544],
  [18314321719503, 46190382812979, 4747350045692, 18130138103744, 51677054828544],
  [18314321719503, 46190382812979, 4747350045692, 22528520945660, 51677054828544],
  [18314321719503, 46190385106739, 4467102330940, 280247714752, 18124768345088],
  [46190382812979, 18314325916879, 4467102330940, 280247714752, 51677054828544]]
def row5 : List (List ℕ) := [
  [18691689349119, 18314321719503, 46190382812979, 4467102330940, 280247714752, 18124768345088],
  [52243975832575, 18314321719503, 46190382812979, 4467102330940, 280247714752, 51677054828544],
  [70088496462911, 18314321719503, 46190382812979, 4467102330940, 18124768345088, 51677054828544],
  [65901641846723, 18314321719503, 46190382812979, 280247714752, 18124768345088, 51677054828544],
  [24178361364684, 18314321719503, 4467102330940, 280247714752, 18124768345088, 51677054828544],
  [52054422458160, 46190382812979, 4467102330940, 280247714752, 18124768345088, 51677054828544],
  [2293760, 18314321719503, 46190382812979, 4467102330940, 280247714752, 18124768345088],
  [18314321719503, 4197376, 46190382812979, 4467102330940, 280247714752, 51677054828544],
  [18314321719503, 46190382812979, 4467102330940, 280247714752, 18124768345088, 51677054828544],
  [18314321719503, 46190382812979, 4467102330940, 280247714752, 18124768345088, 51687943245619],
  [18314321719503, 46190382812979, 4467102330940, 280247714752, 18124768345088, 51746109861948],
  [18314321719503, 46190382812979, 4467102330940, 280247714752, 18124768345088, 51957301494720],
  [18314321719503, 46190382812979, 4467102330940, 280247714752, 18675103169743, 51677054828544],
  [18314321719503, 46190382812979, 4467102330940, 280247714752, 22523151187004, 51677054828544],
  [18314321719503, 46190382812979, 4467102330940, 280247714752, 18130138103744, 51677054828544],
  [18314321719503, 46190382812979, 4467102330940, 4747350045692, 18124768345088, 51677054828544],
  [18314321719503, 46190382812979, 280247714752, 4747350045692, 18124768345088, 51677054828544]]
def row6 : List (List ℕ) := [inputs]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem chk3 : row3.all (fun S => verify width topMask 2 S row2) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem chk4 : row4.all (fun S => verify width topMask 3 S row3) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem chk5 : row5.all (fun S => verify width topMask 4 S row4) = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem chk6 : row6.all (fun S => verify width topMask 5 S row5) = true := by
  decide +kernel

theorem excluded (f : ℕ)
    (hp : ∀ i < width, topMask.testBit i = topMask.testBit (width+i) ∧ f.testBit i ≠ f.testBit (width+i))
    (hc : Can topMask f 6 inputs.toFinset) : False := by
  obtain ⟨S5,h5,c5⟩ := advance hp (List.all_eq_true.mp chk6 inputs (by simp [row6])) hc
  obtain ⟨S4,h4,c4⟩ := advance hp (List.all_eq_true.mp chk5 S5 h5) c5
  obtain ⟨S3,h3,c3⟩ := advance hp (List.all_eq_true.mp chk4 S4 h4) c4
  obtain ⟨S2,h2,c2⟩ := advance hp (List.all_eq_true.mp chk3 S3 h3) c3
  simp [row2] at h2

def target (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4)

def assignment (p : ℕ) (i : Fin 6) : Bool := (inputs.getD i.val 0).testBit p

theorem inputMap (p : ℕ) : List.ofFn (assignment p) = inputs.map (fun t => t.testBit p) := by
  simp [inputs,assignment,List.ofFn_succ]

theorem values : ∀ p : Fin (2*width), target (assignment p.val) = targetBits.testBit p.val ∧
    topMask.testBit p.val = true := by decide +kernel

theorem paired : ∀ i : Fin width, targetBits.testBit i.val ≠ targetBits.testBit (width+i.val) := by
  decide +kernel

theorem lower (t : ℕ) (h : HasCircuitSize 6 target t) : 7 ≤ t := by
  by_contra! ht
  obtain ⟨C,ok,sz,ev⟩ := h
  have hok : ∀ g ∈ C.gates, GOk g := ok
  let out := (tabs topMask inputs C.gates).getD C.output 0
  have obs (p : Fin (2*width)) : out.testBit p.val = targetBits.testBit p.val := by
    have hval := ev (assignment p.val)
    unfold Circuit.eval Circuit.wires at hval
    rw [inputMap,wires_tabs topMask p.val (values p).2 _ _ hok,getD_map_testBit] at hval
    exact hval.trans (values p).1
  have hw : ∀ i < width, topMask.testBit i = topMask.testBit (width+i) ∧ out.testBit i ≠ out.testBit (width+i) := by
    intro i hi
    let p : Fin (2*width) := ⟨i,by omega⟩
    let q : Fin (2*width) := ⟨width+i,by omega⟩
    exact ⟨(values p).2.trans (values q).2.symm,fun e => paired ⟨i,hi⟩ ((obs p).symm.trans (e.trans (obs q)))⟩
  have hc := fromTabs topMask out C.gates inputs hok (getWire _ C.output topMask)
  have pad {k j : ℕ} (hj : k ≤ j) (ha : Can topMask out k inputs.toFinset) : Can topMask out j inputs.toFinset := by
    induction hj with
    | refl => exact ha
    | step _ ih => exact stepUp ih
  change C.gates.length ≤ t at sz
  exact excluded out hw (pad (by omega) hc)

end PEqualNP.Outside.L_meta_5479

theorem PEqualNP.Outside.L_meta_5479 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4)) t → 7 ≤ t := PEqualNP.Outside.L_meta_5479.lower
