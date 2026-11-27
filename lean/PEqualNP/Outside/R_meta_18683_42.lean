import PEqualNP.Defs
theorem PEqualNP.Outside.R_meta_18683_42
    (embed : ∀ (z : Nat → Nat) (a : Nat) (p : Fin 28), (∀ j : Fin 18, ∃ i h : Fin (10 + j.val), z (10 + j.val) = (z i.val ||| z h.val) ∨ z (10 + j.val) = (z i.val &&& z h.val)) →
    ∃ w : Nat → Nat, w 0 = a ∧ (∀ i : Fin 10, w (i.val + 1) = z i.val) ∧
      w 31 = (z p.val ||| (a &&& (z 8 ||| z 9))) ∧ (∀ j : Fin 21, ∃ i h : Fin (11 + j.val), w (11 + j.val) = (w i.val ||| w h.val) ∨ w (11 + j.val) = (w i.val &&& w h.val)))
    (punctured : ∃ z : Nat → Nat, (∀ i : Fin 10, z i.val = ([663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] : List Nat).getD i.val 0) ∧ (∃ p : Fin 28, z p.val ||| 3 = 65535) ∧ (∀ j : Fin 18, ∃ i h : Fin (10 + j.val), z (10 + j.val) = (z i.val ||| z h.val) ∨ z (10 + j.val) = (z i.val &&& z h.val))) :
    ∃ (x1 : ℕ → ℕ), (∀ (x2 : Fin (11 : ℕ)), x1 ↑x2 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x2 (0 : ℕ)) ∧ (∃ (x2 : Fin (32 : ℕ)), x1 ↑x2 = (65535 : ℕ)) ∧ ∀ (x2 : Fin (21 : ℕ)), ∃ (x3 : Fin ((11 : ℕ) + ↑x2)) (x4 : Fin ((11 : ℕ) + ↑x2)), x1 ((11 : ℕ) + ↑x2) = x1 ↑x3 ||| x1 ↑x4 ∨ x1 ((11 : ℕ) + ↑x2) = x1 ↑x3 &&& x1 ↑x4 := by
  obtain ⟨z, init, ⟨p, hp⟩, hz⟩ := punctured
  obtain ⟨w, h0, hshift, hout, hrec⟩ := embed z 2147418115 p hz
  refine ⟨w, ?_, ⟨⟨31, by decide⟩, ?_⟩, hrec⟩
  · intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact h0
    · change w (k.val + 1) = ([2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] : List Nat).getD (k.val+1) 0
      rw [hshift, init]
      rfl
  · have h8 := init (8 : Fin 10)
    have h9 := init (9 : Fin 10)
    change z 8 = 581968119809 at h8
    change z 9 = 1065151898146 at h9
    change w 31 = 65535
    rw [hout,h8,h9]
    exact hp
