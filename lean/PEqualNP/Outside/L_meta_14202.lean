import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14202

open PEqualNP.CircuitLowerBounds

def Free {X : Type} (S : Set (X → Bool)) (f : X → Bool) : Prop :=
  (∃ b, f = fun _ => b) ∨ ∃ w ∈ S, ∃ u : Bool → Bool, f = u ∘ w

def mix {X : Type} (q : Bool → Bool → Bool) (a b : X → Bool) : X → Bool := fun x => q (a x) (b x)

def Can {X : Type} : ℕ → Set (X → Bool) → (X → Bool) → Prop
  | 0, S, f => Free S f
  | k+1, S, f => Free S f ∨ ∃ a ∈ S, ∃ b ∈ S, ∃ q : Bool → Bool → Bool, Can k (insert (mix q a b) S) f

theorem freeMem {X : Type} {S : Set (X → Bool)} {f} (h : f ∈ S) : Free S f :=
  Or.inr ⟨f, h, id, rfl⟩

theorem freeUnary {X : Type} {S : Set (X → Bool)} {f} (h : Free S f) (u : Bool → Bool) :
    Free S (u ∘ f) := by
  rcases h with ⟨c, rfl⟩ | ⟨w, hw, v, rfl⟩
  · exact Or.inl ⟨u c, rfl⟩
  · exact Or.inr ⟨w, hw, u ∘ v, rfl⟩

theorem freeMap {X Y : Type} {S : Set (X → Bool)} {T : Set (Y → Bool)}
    {p : Y → X} {f} (h : Free S f) (hs : ∀ w ∈ S, Free T (w ∘ p)) :
    Free T (f ∘ p) := by
  rcases h with ⟨c, rfl⟩ | ⟨w, hw, v, rfl⟩
  · exact Or.inl ⟨c, rfl⟩
  · exact freeUnary (hs w hw) v

theorem canFree {X : Type} {S : Set (X → Bool)} {f} (k) (h : Free S f) : Can k S f := by
  cases k with
  | zero => exact h
  | succ => exact Or.inl h

theorem canWeaken {X : Type} {S : Set (X → Bool)} {f} {k l : ℕ}
    (h : Can k S f) (hle : k ≤ l) : Can l S f := by
  induction k generalizing l S with
  | zero => exact canFree l h
  | succ k ih =>
    cases l with
    | zero => omega
    | succ l =>
      rcases h with hf | ⟨a, ha, b, hb, q, hn⟩
      · exact Or.inl hf
      · exact Or.inr ⟨a, ha, b, hb, q, ih hn (by omega)⟩

theorem mixFreeCases {X : Type} {T : Set (X → Bool)} {a b} (q : Bool → Bool → Bool)
    (ha : Free T a) (hb : Free T b) :
    Free T (mix q a b) ∨ ∃ r ∈ T, ∃ s ∈ T, ∃ q', mix q a b = mix q' r s := by
  rcases ha with ⟨c, rfl⟩ | ⟨r, hr, u, rfl⟩
  · exact Or.inl (freeUnary hb (q c))
  · rcases hb with ⟨c, rfl⟩ | ⟨s, hs, v, rfl⟩
    · exact Or.inl (Or.inr ⟨r, hr, fun t => q (u t) c, rfl⟩)
    · exact Or.inr ⟨r, hr, s, hs, fun t t' => q (u t) (v t'), rfl⟩

theorem canMap {X Y : Type} {k S f} {p : Y → X} {T : Set (Y → Bool)}
    (h : Can k S f) (hs : ∀ w ∈ S, Free T (w ∘ p)) : Can k T (f ∘ p) := by
  induction k generalizing S T with
  | zero => exact freeMap h hs
  | succ k ih =>
    rcases h with hf | ⟨a, ha, b, hb, q, hn⟩
    · exact Or.inl (freeMap hf hs)
    · rcases mixFreeCases q (hs a ha) (hs b hb) with hh | ⟨r, hr, s, hmem, v, he⟩
      · apply canWeaken (k := k) _ (Nat.le_succ k)
        apply ih hn
        rintro w (rfl | hw)
        · exact hh
        · exact hs w hw
      · refine Or.inr ⟨r, hr, s, hmem, v, ih hn ?_⟩
        rintro w (rfl | hw)
        · exact freeMem (he ▸ Set.mem_insert _ _ : mix q (a ∘ p) (b ∘ p) ∈ insert (mix v r s) T)
        · exact freeMap (p := id) (hs w hw) (fun t ht => freeMem (Set.mem_insert_of_mem _ ht))

theorem saveGate {X Y : Type} {k S f} {p : Y → X} {T : Set (Y → Bool)}
    (x y : X) (hxy : f x ≠ f y) (hnc : ¬ ∃ c, f ∘ p = fun _ => c)
    (h : Can k S f) (hs : ∀ w ∈ S, Free T (w ∘ p))
    (hd : ∀ w ∈ S, w x = w y ∨ ∃ c, w ∘ p = fun _ => c) :
    ∃ j < k, Can j T (f ∘ p) := by
  have term (U : Set (X → Bool)) (hu : Free U f)
      (hm : ∀ w ∈ U, w x = w y ∨ ∃ c, w ∘ p = fun _ => c) : False := by
    rcases hu with ⟨c, he⟩ | ⟨w, hw, u, he⟩
    · exact hxy (he ▸ rfl)
    · rcases hm w hw with hh | ⟨c, hc⟩
      · exact hxy (he ▸ congrArg u hh)
      · apply hnc
        exact ⟨u c, he ▸ congrArg (fun t => u ∘ t) hc⟩
  induction k generalizing S T with
  | zero => exact (term S h hd).elim
  | succ k ih =>
    rcases h with hf | ⟨a, ha, b, hb, q, hq⟩
    · exact (term S hf hd).elim
    · by_cases ab : a x = a y ∧ b x = b y
      · rcases mixFreeCases q (hs a ha) (hs b hb) with hc | ⟨r, hr, s, hmem, v, he⟩
        · obtain ⟨j, hj, hcan⟩ := ih hq (T := T) (by
            rintro w (rfl | hw)
            · exact hc
            · exact hs w hw) (by
            rintro w (rfl | hw)
            · exact Or.inl (by simp [mix, ab.1, ab.2])
            · exact hd w hw)
          exact ⟨j, by omega, hcan⟩
        · obtain ⟨j, hj, hcan⟩ := ih hq (T := insert (mix v r s) T) (by
            rintro w (rfl | hw)
            · apply freeMem
              change mix q (a ∘ p) (b ∘ p) ∈ _
              rw [he]
              exact Set.mem_insert _ _
            · exact freeMap (p := id) (hs w hw) (fun t ht => freeMem (Set.mem_insert_of_mem _ ht))) (by
            rintro w (rfl | hw)
            · exact Or.inl (by simp [mix, ab.1, ab.2])
            · exact hd w hw)
          exact ⟨j+1, by omega, Or.inr ⟨r, hr, s, hmem, v, hcan⟩⟩
      · refine ⟨k, by omega, canMap hq ?_⟩
        rintro w (rfl | hw)
        · change Free T (mix q (a ∘ p) (b ∘ p))
          by_cases eq : a x = a y
          · obtain ⟨c, hc⟩ := (hd b hb).resolve_left (fun h => ab ⟨eq, h⟩)
            rw [hc]
            exact freeUnary (hs a ha) (fun t => q t c)
          · obtain ⟨c, hc⟩ := (hd a ha).resolve_left eq
            rw [hc]
            exact freeUnary (hs b hb) (q c)
        · exact hs w hw

abbrev cols (n : ℕ) := Set.range (fun i : Fin n => fun x : Fin n → Bool => x i)

def front {n : ℕ} (b : Bool) (x : Fin n → Bool) : Fin (n+1) → Bool := Fin.cons b x

def separates {n : ℕ} (f : (Fin (n+1) → Bool) → Bool) (i : Fin n) : Prop :=
  f (front false (fun j => decide (j = i))) ≠ f (front true (fun j => decide (j = i)))

def remains {n : ℕ} (f : (Fin (n+1) → Bool) → Bool) : Prop :=
  f (front false (fun _ => false)) ≠ f (front false (fun _ => true))

theorem removeFront {n k : ℕ} (f : (Fin (n+1) → Bool) → Bool) (i : Fin n)
    (h : Can k (cols (n+1)) f) (hd : separates f i) (hn : remains f) :
    ∃ j < k, Can j (cols n) (f ∘ front false) := by
  refine saveGate _ _ hd ?_ h ?_ ?_
  · rintro ⟨c, hc⟩
    exact hn ((congrFun hc (fun _ => false)).trans (congrFun hc (fun _ => true)).symm)
  · rintro _ ⟨t, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) t
    · exact Or.inl ⟨false, rfl⟩
    · apply freeMem
      exact ⟨j, by funext x; simp [front]⟩
  · rintro _ ⟨t, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) t
    · exact Or.inr ⟨false, rfl⟩
    · exact Or.inl (by simp [front])

def edges : List ℕ := [0,4,0,5,1,5,4,5,0,6,1,6,4,6,0,7,2,7,3,7,4,7]

def target (x : Fin 8 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def perm : Fin 8 → Fin 8 := ![5,4,1,0,6,7,3,2]
def f8 (x : Fin 8 → Bool) := target (x ∘ perm)
def f7 := f8 ∘ front false
def f6 := f7 ∘ front false
def f5 := f6 ∘ front false
def f4 := f5 ∘ front false
def f3 := f4 ∘ front false

theorem core {k} (hk : Can k (cols 8) target) : ∃ j, j+5 ≤ k ∧ Can j (cols 3) f3 := by
  have h8 : Can k (cols 8) f8 := by
    apply canMap (p := fun x => x ∘ perm) hk
    rintro _ ⟨i, rfl⟩
    exact freeMem ⟨perm i, rfl⟩
  obtain ⟨a, ha, h7⟩ := removeFront f8 1 h8 (by unfold separates; decide) (by unfold remains; decide)
  obtain ⟨b, hb, h6⟩ := removeFront f7 0 h7 (by unfold separates; decide) (by unfold remains; decide)
  obtain ⟨c, hc, h5⟩ := removeFront f6 2 h6 (by unfold separates; decide) (by unfold remains; decide)
  obtain ⟨d, hd, h4⟩ := removeFront f5 1 h5 (by unfold separates; decide) (by unfold remains; decide)
  obtain ⟨e, he, h3⟩ := removeFront f4 2 h4 (by unfold separates; decide) (by unfold remains; decide)
  exact ⟨e, by omega, h3⟩

theorem f3_eq : f3 = fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) := by
  apply funext
  decide +kernel

def witness : Circuit := ⟨[
  ⟨.or,[0,4]⟩, ⟨.or,[5,6]⟩, ⟨.or,[2,3]⟩, ⟨.and,[0,4]⟩,
  ⟨.or,[8,1]⟩, ⟨.and,[12,9]⟩, ⟨.or,[8,10]⟩, ⟨.and,[14,7]⟩,
  ⟨.or,[11,13]⟩, ⟨.or,[16,15]⟩], 17⟩

theorem witness_ok : ∀ g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem witness_eval : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

def compGate {X : Type} (w : X → List Bool) (g : Gate) : X → Bool :=
  fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)

theorem compNot {X : Type} {S : Set (X → Bool)} (w : X → List Bool) (g : Gate)
    (h : g.op = .not) (hw : ∀ i, Free S (fun x => (w x).getD i false)) : Free S (compGate w g) := by
  rcases g with ⟨op, args⟩
  change op = .not at h
  subst op
  cases args with
  | nil => exact Or.inl ⟨true, rfl⟩
  | cons i rest => exact freeUnary (hw i) Bool.not

theorem compArity {X : Type} {S : Set (X → Bool)} (w : X → List Bool) (g : Gate)
    (h : g.inputs.length ≤ 2) (hw : ∀ i, Free S (fun x => (w x).getD i false)) :
    Free S (compGate w g) ∨ ∃ a ∈ S, ∃ b ∈ S, ∃ q : Bool → Bool → Bool, compGate w g = mix q a b := by
  rcases g with ⟨op, args⟩
  cases args with
  | nil => exact Or.inl (Or.inl ⟨op.eval [], rfl⟩)
  | cons i rest =>
    cases rest with
    | nil => exact Or.inl (freeUnary (hw i) (fun z => op.eval [z]))
    | cons j rest =>
      cases rest with
      | nil => exact mixFreeCases (fun z t => op.eval [z, t]) (hw i) (hw j)
      | cons k rest =>
        change (i :: j :: k :: rest).length ≤ 2 at h
        simp only [List.length_cons] at h
        omega

theorem compAppend {X : Type} {S : Set (X → Bool)} (w : X → List Bool) (l : ℕ)
    (hl : ∀ x, (w x).length = l) (hw : ∀ i, Free S (fun x => (w x).getD i false))
    (v : X → Bool) (hv : Free S v) (i : ℕ) : Free S (fun x => (w x ++ [v x]).getD i false) := by
  by_cases hi : i < l
  · have e : (fun x => (w x ++ [v x]).getD i false) = fun x => (w x).getD i false := by
      funext x
      exact List.getD_append _ _ _ _ (by rw [hl x]; exact hi)
    rw [e]
    exact hw i
  · by_cases he : i = l
    · subst i
      have e : (fun x => (w x ++ [v x]).getD l false) = v := by
        funext x
        rw [List.getD_append_right _ _ _ _ (hl x).le, hl x, Nat.sub_self]
        rfl
      rw [e]
      exact hv
    · refine Or.inl ⟨false, ?_⟩
      funext x
      apply List.getD_eq_default
      simp only [List.length_append, List.length_singleton, hl x]
      omega

def compFlag (g : Gate) : Bool := match g.op with | .not => false | _ => true

theorem compBuild {X : Type} (gs : List Gate) (o : ℕ) :
    ∀ (S : Set (X → Bool)) (w : X → List Bool) (l : ℕ), (∀ x, (w x).length = l) →
    (∀ i, Free S (fun x => (w x).getD i false)) → (∀ g ∈ gs, g.inputs.length ≤ 2) →
    Can (gs.filter compFlag).length S (fun x => (Circuit.mk gs o).eval (w x)) := by
  induction gs with
  | nil =>
    intro S w l hl hw hg
    exact hw o
  | cons g gs ih =>
    intro S w l hl hw hg
    let v := compGate w g
    let ww : X → List Bool := fun x => w x ++ [v x]
    have hlen : ∀ x, (ww x).length = l + 1 := by simp [ww, hl]
    have go (T : Set (X → Bool)) (ht : ∀ i, Free T (fun x => (w x).getD i false)) (hv : Free T v) :
        Can (gs.filter compFlag).length T (fun x => (Circuit.mk (g :: gs) o).eval (w x)) :=
      ih T ww (l + 1) hlen (compAppend w l hl ht v hv) (fun a ha => hg a (List.mem_cons_of_mem g ha))
    cases hflag : compFlag g with
    | false =>
      have hop : g.op = .not := by cases e : g.op <;> simp [compFlag, e] at hflag ⊢
      simpa [List.filter_cons, hflag] using go S hw (compNot w g hop hw)
    | true =>
      have hlenGate : ((g :: gs).filter compFlag).length = (gs.filter compFlag).length + 1 := by
        simp [hflag]
      rw [hlenGate]
      rcases compArity w g (hg g (List.mem_cons_self ..)) hw with hf | ⟨a, ha, b, hb, q, he⟩
      · exact canWeaken (go S hw hf) (Nat.le_succ _)
      · refine Or.inr ⟨a, ha, b, hb, q, go (insert (mix q a b) S) (fun i =>
          freeMap (p := id) (hw i) (fun t ht => freeMem (Set.mem_insert_of_mem _ ht))) ?_⟩
        apply freeMem
        change compGate w g ∈ insert (mix q a b) S
        rw [he]
        exact Set.mem_insert _ _

theorem compile {n : ℕ} (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    Can (gs.filter compFlag).length (cols n) (fun x => (Circuit.mk gs o).eval (List.ofFn x)) := by
  refine compBuild gs o _ (fun x : Fin n → Bool => List.ofFn x) n (fun _ => List.length_ofFn) ?_ (fun g h => (hg g h).2)
  intro i
  by_cases h : i < n
  · refine Or.inr ⟨(fun x : Fin n → Bool => x ⟨i, h⟩), ⟨⟨i, h⟩, rfl⟩, id, ?_⟩
    funext x
    simp [List.getD_eq_getElem?_getD, h]
  · refine Or.inl ⟨false, ?_⟩
    funext x
    apply List.getD_eq_default
    simpa using (Nat.le_of_not_gt h)

theorem comp_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) :
    (gs.filter compFlag).length < gs.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  obtain ⟨g, hg, hop⟩ := h
  exact ⟨g, hg, by simp [compFlag, hop]⟩

def majWord (w : (Fin 3 → Bool) → Bool) : BitVec 8 :=
  BitVec.cons (w ![true, true, true]) (BitVec.cons (w ![true, true, false])
    (BitVec.cons (w ![true, false, true]) (BitVec.cons (w ![true, false, false])
    (BitVec.cons (w ![false, true, true]) (BitVec.cons (w ![false, true, false])
    (BitVec.cons (w ![false, false, true]) (BitVec.cons (w ![false, false, false]) (0 : BitVec 0))))))))

def majCode (w : (Fin 3 → Bool) → Bool) : ℕ := (majWord w).toNat

lemma majAnd (a b : (Fin 3 → Bool) → Bool) :
    majCode (fun x => a x && b x) = majCode a &&& majCode b := by
  unfold majCode
  rw [← BitVec.toNat_and]
  simp only [majWord, BitVec.cons_and_cons]
  rfl

lemma majXor (a b : (Fin 3 → Bool) → Bool) :
    majCode (fun x => a x ^^ b x) = majCode a ^^^ majCode b := by
  unfold majCode
  rw [← BitVec.toNat_xor]
  simp only [majWord, BitVec.cons_xor_cons]
  rfl

def majSum (k a r : Bool) : Bool := if k then a ^^ r else r

def majAdd (a : ℕ) (s : List ℕ) : List ℕ := s ++ s.map (fun r => a ^^^ r)

lemma majSumMem {s : List ℕ} (k : Bool) (a w : (Fin 3 → Bool) → Bool)
    (hw : majCode w ∈ s) : majCode (fun x => majSum k (a x) (w x)) ∈ majAdd (majCode a) s := by
  cases k with
  | false => exact List.mem_append_left _ hw
  | true =>
    change majCode (fun x => a x ^^ w x) ∈ s ++ _
    rw [majXor]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, hw, rfl⟩)

def majOps (a b : ℕ) : List ℕ := majAdd 255 (majAdd a (majAdd b (majAdd (a &&& b) [0])))

lemma majPoly (q : Bool → Bool → Bool) : ∃ k l m n : Bool, ∀ a b : Bool,
    q a b = majSum k true (majSum l a (majSum m b (majSum n (a && b) false))) := by
  refine ⟨q false false, q true false ^^ q false false, q false true ^^ q false false,
    q true true ^^ q true false ^^ q false true ^^ q false false, ?_⟩
  intro a b
  cases a <;> cases b <;> cases q false false <;> cases q true false <;>
    cases q false true <;> cases q true true <;> rfl

lemma majMixMem (q : Bool → Bool → Bool) (a b : (Fin 3 → Bool) → Bool) :
    majCode (mix q a b) ∈ majOps (majCode a) (majCode b) := by
  obtain ⟨k, l, m, n, hp⟩ := majPoly q
  have e : mix q a b = fun x => majSum k true (majSum l (a x) (majSum m (b x)
      (majSum n (a x && b x) false))) := funext fun x => hp (a x) (b x)
  rw [e]
  unfold majOps
  apply majSumMem k (fun _ => true)
  apply majSumMem l a
  apply majSumMem m b
  rw [← majAnd a b]
  apply majSumMem n (fun x => a x && b x) (fun _ => false)
  exact List.Mem.head _

def majNext (s : List ℕ) : List ℕ :=
  (s.flatMap fun a => s.flatMap fun b => majOps a b).eraseDups

def majHit (s : List ℕ) : Bool :=
  s.any fun a => s.any fun b => (majOps a b).contains 232

def majVars : List ℕ := [240, 204, 170]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma majExhaust : ((majNext majVars).any fun u =>
    (majNext (u :: majVars)).any fun v => majHit (v :: u :: majVars)) = false := by
  decide +kernel

lemma majPad {X : Type} {n : ℕ} {S : Set (X → Bool)} {w f : X → Bool}
    (hw : w ∈ S) (h : Can (n + 1) S f) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ q : Bool → Bool → Bool, Can n (insert (mix q a b) S) f := by
  rcases h with h | h
  · refine ⟨w, hw, w, hw, (fun x _ => x), ?_⟩
    have hf : Free (insert (mix (fun x _ => x) w w) S) f := by
      rcases h with hc | ⟨v, hv, u, hu⟩
      · exact Or.inl hc
      · exact Or.inr ⟨v, Set.mem_insert_of_mem _ hv, u, hu⟩
    cases n with
    | zero => exact hf
    | succ n => exact Or.inl hf
  · exact h

lemma majLast {X : Type} {S : Set (X → Bool)} {w f : X → Bool}
    (hw : w ∈ S) (h : Can 1 S f) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ q : Bool → Bool → Bool, f = mix q a b := by
  obtain ⟨a, ha, b, hb, q, hf⟩ := majPad (n := 0) hw h
  rcases hf with ⟨k, hk⟩ | ⟨v, hv, u, hu⟩
  · exact ⟨w, hw, w, hw, fun _ _ => k, hk⟩
  · rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact ⟨a, ha, b, hb, fun x y => u (q x y), hu⟩
    · exact ⟨v, hv, v, hv, fun x _ => u x, hu⟩

def majRep (S : Set ((Fin 3 → Bool) → Bool)) (s : List ℕ) : Prop :=
  ∀ w ∈ S, majCode w ∈ s

lemma majExtend {S : Set ((Fin 3 → Bool) → Bool)} {s : List ℕ} {a b : (Fin 3 → Bool) → Bool}
    (hr : majRep S s) (ha : a ∈ S) (hb : b ∈ S) (q : Bool → Bool → Bool) :
    majCode (mix q a b) ∈ majNext s ∧ majRep (insert (mix q a b) S) (majCode (mix q a b) :: s) := by
  constructor
  · apply List.mem_eraseDups.mpr
    exact List.mem_flatMap.mpr ⟨_, hr a ha, List.mem_flatMap.mpr ⟨_, hr b hb, majMixMem q a b⟩⟩
  · intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · exact List.Mem.head _
    · exact List.mem_cons_of_mem _ (hr w hw)

theorem majLower : ¬ Can 3 (Set.range (fun i : Fin 3 => fun x : Fin 3 → Bool => x i))
    (fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) := by
  let S := Set.range (fun i : Fin 3 => fun x : Fin 3 → Bool => x i)
  let f := fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)
  change ¬ Can 3 S f
  intro h
  have hr : majRep S majVars := by
    rintro w ⟨i, rfl⟩
    fin_cases i <;> decide
  have hw : (fun x : Fin 3 → Bool => x 0) ∈ S := ⟨0, rfl⟩
  obtain ⟨a, ha, b, hb, q, h1⟩ := majPad (n := 2) hw h
  obtain ⟨hu, hr1⟩ := majExtend hr ha hb q
  obtain ⟨c, hc, d, hd, r, h2⟩ := majPad (n := 1) (Set.mem_insert (mix q a b) S) h1
  obtain ⟨hv, hr2⟩ := majExtend hr1 hc hd r
  obtain ⟨e, he, g, hg, t, ht⟩ := majLast (Set.mem_insert (mix r c d) _) h2
  have hmem : 232 ∈ majOps (majCode e) (majCode g) := by
    have hf : majCode f = 232 := by unfold f; decide +kernel
    rw [← hf, ht]
    exact majMixMem t e g
  have hs : majHit (majCode (mix r c d) :: majCode (mix q a b) :: majVars) = true :=
    List.any_eq_true.mpr ⟨_, hr2 e he, List.any_eq_true.mpr ⟨_, hr2 g hg, List.contains_iff_mem.mpr hmem⟩⟩
  have hyes : ((majNext majVars).any fun u =>
      (majNext (u :: majVars)).any fun v => majHit (v :: u :: majVars)) = true :=
    List.any_eq_true.mpr ⟨_, hu, List.any_eq_true.mpr ⟨_, hv, hs⟩⟩
  rw [majExhaust] at hyes
  contradiction

end PEqualNP.Outside.L_meta_14202

theorem PEqualNP.Outside.L_meta_14202 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 4, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o hg _ he
  by_cases hn : ∃ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · have h := PEqualNP.Outside.L_meta_14202.compile (n := 8) gs o hg
    have heq : (fun x => (PEqualNP.CircuitLowerBounds.Circuit.mk gs o).eval (List.ofFn x)) =
        PEqualNP.Outside.L_meta_14202.target := funext he
    rw [heq] at h
    obtain ⟨j, hj, hc⟩ := PEqualNP.Outside.L_meta_14202.core h
    have hlarge : 3 < j := by
      by_contra! hle
      rw [PEqualNP.Outside.L_meta_14202.f3_eq] at hc
      exact PEqualNP.Outside.L_meta_14202.majLower (PEqualNP.Outside.L_meta_14202.canWeaken hc hle)
    have hlen := PEqualNP.Outside.L_meta_14202.comp_lt gs hn
    refine ⟨PEqualNP.Outside.L_meta_14202.witness.gates, PEqualNP.Outside.L_meta_14202.witness.output,
      PEqualNP.Outside.L_meta_14202.witness_ok, ?_, PEqualNP.Outside.L_meta_14202.witness_eval⟩
    change 10 ≤ gs.length
    omega
  · refine ⟨gs, o, ?_, le_rfl, he⟩
    intro g hm
    obtain ⟨ha | ho | hnot, hsize⟩ := hg g hm
    · exact ⟨Or.inl ha, hsize⟩
    · exact ⟨Or.inr ho, hsize⟩
    · exact (hn ⟨g, hm, hnot⟩).elim
