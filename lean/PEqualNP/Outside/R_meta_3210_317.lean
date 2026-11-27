import Mathlib
import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3210_317
    (h0 : have x1 : List ℕ := [(515 : ℕ), (518 : ℕ), (12 : ℕ), (529 : ℕ), (24 : ℕ), (545 : ℕ), (578 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (562 : ℕ), (581 : ℕ), (104 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (914 : ℕ)]; ¬ FormulaSat ((PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)) ++ ([[P (ix 10 14 0 13 0)], [P (ix 10 14 2 13 22)], (List.range 12).map (fun t => P (ix 10 14 1 13 (10+t)))] : List (List ℕ))))
    (h1 : have x1 : List ℕ := [(515 : ℕ), (518 : ℕ), (12 : ℕ), (529 : ℕ), (24 : ℕ), (545 : ℕ), (578 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (562 : ℕ), (581 : ℕ), (104 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (914 : ℕ)]; ¬ FormulaSat ((PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)) ++ ([[P (ix 10 14 0 13 1)], [P (ix 10 14 2 13 22)], (List.range 12).map (fun t => P (ix 10 14 1 13 (10+t)))] : List (List ℕ))))
    : have x1 : List ℕ := [(515 : ℕ), (518 : ℕ), (12 : ℕ), (529 : ℕ), (24 : ℕ), (545 : ℕ), (578 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (562 : ℕ), (581 : ℕ), (104 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (914 : ℕ)]; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)) := by
  let yesRows : List ℕ := [515, 518, 12, 529, 24, 545, 578, 132, 160, 264, 288, 320]
  let noRows : List ℕ := [554, 562, 581, 104, 116, 650, 713, 208, 773, 276, 897, 914]
  let rows := yesRows ++ noRows
  let g := fun r => yesRows.contains r
  change ¬ FormulaSat (enc 10 14 g rows)
  rintro ⟨a, ha⟩
  change ∀ c ∈ enc 10 14 g rows, ClauseSat a c at ha
  have negEq (b : Bool) : (b = false) ↔ ¬ b = true := by cases b <;> decide
  have usefGate (c : List ℕ) (hc : c ∈ fGate 10 14 rows) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc)))))))))
  have usefOp (c : List ℕ) (hc : c ∈ fOp 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc)))))))))))
  have usefOrd (c : List ℕ) (hc : c ∈ fOrd 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inr hc))
  have usefOut (c : List ℕ) (hc : c ∈ fOut 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))))
  have usefOutAlo (c : List ℕ) (hc : c ∈ fOutAlo 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))))))
  have usefOutEq (c : List ℕ) (hc : c ∈ fOutEq 10 14 g rows) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc)))))))
  have usefPad (c : List ℕ) (hc : c ∈ fPad 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc)))))
  have usefPadRd (c : List ℕ) (hc : c ∈ fPadRd 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inr hc)))
  have usefPre (c : List ℕ) (hc : c ∈ fPre 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inr hc))))
  have usefSrcAlo (c : List ℕ) (hc : c ∈ fSrcAlo 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc)))))))))))
  have usefSrcEq (c : List ℕ) (hc : c ∈ fSrcEq 10 14 rows) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))))))))
  have usefUsed (c : List ℕ) (hc : c ∈ fUsed 10 14) : ClauseSat a c := by
    apply ha
    change c ∈ fOp 10 14 ++ fSrcAlo 10 14 ++ fSrcEq 10 14 rows ++ fGate 10 14 rows ++ fOutAlo 10 14 ++ fOutEq 10 14 g rows ++ fOut 10 14 ++ fPad 10 14 ++ fPre 10 14 ++ fPadRd 10 14 ++ fOrd 10 14 ++ fUsed 10 14
    simp only [List.mem_append]
    exact (Or.inr hc)
  have cl0 : ¬ a 123783 = true ∨ a 13640 = true := by
    have hc := usefPad [247567, 27280] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([247567, 27280] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl1 : ¬ a 123783 = true ∨ a 122734 = true := by
    have hc := usefPre [247567, 245468] (by
      exact List.mem_map.mpr ⟨12, by decide, rfl⟩)
    change ∃ l ∈ ([247567, 245468] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl2 : ¬ a 122734 = true ∨ ¬ a 45130 = true := by
    have hc := usefPadRd [245469, 90261] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([245469, 90261] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl3 : ¬ a 122734 = true ∨ ¬ a 29395 = true := by
    have hc := usefPadRd [245469, 58791] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([245469, 58791] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl4 : ¬ a 122734 = true ∨ a 12591 = true := by
    have hc := usefPad [245469, 25182] (by
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([245469, 25182] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl5 : ¬ a 122734 = true ∨ a 121685 = true := by
    have hc := usefPre [245469, 243370] (by
      exact List.mem_map.mpr ⟨11, by decide, rfl⟩)
    change ∃ l ∈ ([245469, 243370] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl6 : ¬ a 121685 = true ∨ ¬ a 45129 = true := by
    have hc := usefPadRd [243371, 90259] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨11, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([243371, 90259] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl7 : ¬ a 121685 = true ∨ ¬ a 29394 = true := by
    have hc := usefPadRd [243371, 58789] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨11, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([243371, 58789] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl8 : ¬ a 121685 = true ∨ a 11542 = true := by
    have hc := usefPad [243371, 23084] (by
      refine List.mem_flatMap.mpr ⟨11, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([243371, 23084] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl9 : ¬ a 121685 = true ∨ a 120636 = true := by
    have hc := usefPre [243371, 241272] (by
      exact List.mem_map.mpr ⟨10, by decide, rfl⟩)
    change ∃ l ∈ ([243371, 241272] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl10 : ¬ a 120636 = true ∨ ¬ a 45128 = true := by
    have hc := usefPadRd [241273, 90257] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨10, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([241273, 90257] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl11 : ¬ a 120636 = true ∨ ¬ a 29393 = true := by
    have hc := usefPadRd [241273, 58787] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨10, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([241273, 58787] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl12 : ¬ a 120636 = true ∨ a 10493 = true := by
    have hc := usefPad [241273, 20986] (by
      refine List.mem_flatMap.mpr ⟨10, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([241273, 20986] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl13 : ¬ a 120636 = true ∨ a 119587 = true := by
    have hc := usefPre [241273, 239174] (by
      exact List.mem_map.mpr ⟨9, by decide, rfl⟩)
    change ∃ l ∈ ([241273, 239174] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl14 : ¬ a 119587 = true ∨ ¬ a 45127 = true := by
    have hc := usefPadRd [239175, 90255] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([239175, 90255] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl15 : ¬ a 119587 = true ∨ ¬ a 29392 = true := by
    have hc := usefPadRd [239175, 58785] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([239175, 58785] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl16 : ¬ a 119587 = true ∨ a 9444 = true := by
    have hc := usefPad [239175, 18888] (by
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([239175, 18888] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl17 : ¬ a 119587 = true ∨ a 118538 = true := by
    have hc := usefPre [239175, 237076] (by
      exact List.mem_map.mpr ⟨8, by decide, rfl⟩)
    change ∃ l ∈ ([239175, 237076] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl18 : ¬ a 118538 = true ∨ ¬ a 45126 = true := by
    have hc := usefPadRd [237077, 90253] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([237077, 90253] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl19 : ¬ a 118538 = true ∨ ¬ a 29391 = true := by
    have hc := usefPadRd [237077, 58783] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([237077, 58783] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl20 : ¬ a 118538 = true ∨ a 8395 = true := by
    have hc := usefPad [237077, 16790] (by
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([237077, 16790] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl21 : ¬ a 118538 = true ∨ a 117489 = true := by
    have hc := usefPre [237077, 234978] (by
      exact List.mem_map.mpr ⟨7, by decide, rfl⟩)
    change ∃ l ∈ ([237077, 234978] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl22 : ¬ a 117489 = true ∨ ¬ a 45125 = true := by
    have hc := usefPadRd [234979, 90251] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([234979, 90251] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl23 : ¬ a 117489 = true ∨ ¬ a 29390 = true := by
    have hc := usefPadRd [234979, 58781] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([234979, 58781] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl24 : ¬ a 117489 = true ∨ a 7346 = true := by
    have hc := usefPad [234979, 14692] (by
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([234979, 14692] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl25 : ¬ a 117489 = true ∨ a 116440 = true := by
    have hc := usefPre [234979, 232880] (by
      exact List.mem_map.mpr ⟨6, by decide, rfl⟩)
    change ∃ l ∈ ([234979, 232880] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl26 : ¬ a 116440 = true ∨ ¬ a 45124 = true := by
    have hc := usefPadRd [232881, 90249] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([232881, 90249] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl27 : ¬ a 116440 = true ∨ ¬ a 29389 = true := by
    have hc := usefPadRd [232881, 58779] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([232881, 58779] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl28 : ¬ a 116440 = true ∨ a 6297 = true := by
    have hc := usefPad [232881, 12594] (by
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([232881, 12594] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl29 : ¬ a 116440 = true ∨ a 115391 = true := by
    have hc := usefPre [232881, 230782] (by
      exact List.mem_map.mpr ⟨5, by decide, rfl⟩)
    change ∃ l ∈ ([232881, 230782] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl30 : ¬ a 115391 = true ∨ ¬ a 45123 = true := by
    have hc := usefPadRd [230783, 90247] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([230783, 90247] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl31 : ¬ a 115391 = true ∨ ¬ a 29388 = true := by
    have hc := usefPadRd [230783, 58777] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([230783, 58777] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl32 : ¬ a 115391 = true ∨ a 5248 = true := by
    have hc := usefPad [230783, 10496] (by
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([230783, 10496] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl33 : ¬ a 115391 = true ∨ a 114342 = true := by
    have hc := usefPre [230783, 228684] (by
      exact List.mem_map.mpr ⟨4, by decide, rfl⟩)
    change ∃ l ∈ ([230783, 228684] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl34 : ¬ a 114342 = true ∨ ¬ a 45122 = true := by
    have hc := usefPadRd [228685, 90245] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([228685, 90245] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl35 : ¬ a 114342 = true ∨ ¬ a 29387 = true := by
    have hc := usefPadRd [228685, 58775] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([228685, 58775] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl36 : ¬ a 114342 = true ∨ a 4199 = true := by
    have hc := usefPad [228685, 8398] (by
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([228685, 8398] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl37 : ¬ a 114342 = true ∨ a 113293 = true := by
    have hc := usefPre [228685, 226586] (by
      exact List.mem_map.mpr ⟨3, by decide, rfl⟩)
    change ∃ l ∈ ([228685, 226586] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl38 : ¬ a 113293 = true ∨ ¬ a 45121 = true := by
    have hc := usefPadRd [226587, 90243] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([226587, 90243] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl39 : ¬ a 113293 = true ∨ ¬ a 29386 = true := by
    have hc := usefPadRd [226587, 58773] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([226587, 58773] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl40 : ¬ a 113293 = true ∨ a 3150 = true := by
    have hc := usefPad [226587, 6300] (by
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([226587, 6300] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl41 : ¬ a 113293 = true ∨ a 112244 = true := by
    have hc := usefPre [226587, 224488] (by
      exact List.mem_map.mpr ⟨2, by decide, rfl⟩)
    change ∃ l ∈ ([226587, 224488] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl42 : ¬ a 112244 = true ∨ ¬ a 45120 = true := by
    have hc := usefPadRd [224489, 90241] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([224489, 90241] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl43 : ¬ a 112244 = true ∨ ¬ a 29385 = true := by
    have hc := usefPadRd [224489, 58771] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([224489, 58771] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl44 : ¬ a 112244 = true ∨ a 2101 = true := by
    have hc := usefPad [224489, 4202] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([224489, 4202] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl45 : ¬ a 112244 = true ∨ a 111195 = true := by
    have hc := usefPre [224489, 222390] (by
      exact List.mem_map.mpr ⟨1, by decide, rfl⟩)
    change ∃ l ∈ ([224489, 222390] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl46 : ¬ a 111195 = true ∨ ¬ a 45119 = true := by
    have hc := usefPadRd [222391, 90239] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([222391, 90239] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl47 : ¬ a 111195 = true ∨ ¬ a 29384 = true := by
    have hc := usefPadRd [222391, 58769] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([222391, 58769] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl48 : ¬ a 111195 = true ∨ a 1052 = true := by
    have hc := usefPad [222391, 2104] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([222391, 2104] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl49 : ¬ a 111195 = true ∨ a 110146 = true := by
    have hc := usefPre [222391, 220292] (by
      exact List.mem_map.mpr ⟨0, by decide, rfl⟩)
    change ∃ l ∈ ([222391, 220292] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl50 : ¬ a 110146 = true ∨ a 3 = true := by
    have hc := usefPad [220293, 6] (by
      refine List.mem_flatMap.mpr ⟨0, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([220293, 6] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl51 : ¬ a 94435 = true := by
    have hc := usefOutEq [188871] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨24, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188871] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl52 : ¬ a 94434 = true ∨ ¬ a 61616 = true := by
    have hc := usefOutEq [188869, 123233] (by
      refine List.mem_flatMap.mpr ⟨773, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨23, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188869, 123233] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl53 : ¬ a 94434 = true ∨ ¬ a 61493 = true := by
    have hc := usefOutEq [188869, 122987] (by
      refine List.mem_flatMap.mpr ⟨650, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨23, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188869, 122987] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl54 : ¬ a 94434 = true ∨ ¬ a 61424 = true := by
    have hc := usefOutEq [188869, 122849] (by
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨23, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188869, 122849] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl55 : ¬ a 94434 = true ∨ ¬ a 61405 = true := by
    have hc := usefOutEq [188869, 122811] (by
      refine List.mem_flatMap.mpr ⟨562, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨23, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188869, 122811] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl56 : ¬ a 94434 = true ∨ ¬ a 61397 = true := by
    have hc := usefOutEq [188869, 122795] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨23, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188869, 122795] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl57 : ¬ a 94434 = true ∨ a 60855 = true := by
    have hc := usefOutEq [188869, 121710] (by
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨23, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188869, 121710] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl58 : ¬ a 94434 = true ∨ a 61358 = true := by
    have hc := usefOutEq [188869, 122716] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨23, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188869, 122716] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl59 : ¬ a 94434 = true ∨ a 61361 = true := by
    have hc := usefOutEq [188869, 122722] (by
      refine List.mem_flatMap.mpr ⟨518, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨23, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188869, 122722] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl60 : ¬ a 94433 = true ∨ ¬ a 60348 = true := by
    have hc := usefOutEq [188867, 120697] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188867, 120697] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl61 : ¬ a 94432 = true ∨ ¬ a 59299 = true := by
    have hc := usefOutEq [188865, 118599] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨21, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188865, 118599] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl62 : ¬ a 94431 = true ∨ ¬ a 58250 = true := by
    have hc := usefOutEq [188863, 116501] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨20, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188863, 116501] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl63 : ¬ a 94430 = true ∨ ¬ a 57201 = true := by
    have hc := usefOutEq [188861, 114403] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨19, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188861, 114403] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl64 : ¬ a 94429 = true ∨ ¬ a 56152 = true := by
    have hc := usefOutEq [188859, 112305] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨18, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188859, 112305] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl65 : ¬ a 94428 = true ∨ ¬ a 55103 = true := by
    have hc := usefOutEq [188857, 110207] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨17, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188857, 110207] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl66 : ¬ a 94427 = true ∨ ¬ a 54054 = true := by
    have hc := usefOutEq [188855, 108109] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨16, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188855, 108109] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl67 : ¬ a 94426 = true ∨ ¬ a 53005 = true := by
    have hc := usefOutEq [188853, 106011] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨15, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188853, 106011] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl68 : ¬ a 94425 = true ∨ ¬ a 51956 = true := by
    have hc := usefOutEq [188851, 103913] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨14, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188851, 103913] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl69 : ¬ a 94424 = true ∨ ¬ a 50907 = true := by
    have hc := usefOutEq [188849, 101815] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188849, 101815] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl70 : ¬ a 94423 = true ∨ ¬ a 49858 = true := by
    have hc := usefOutEq [188847, 99717] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188847, 99717] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl71 : ¬ a 94422 = true ∨ ¬ a 48809 = true := by
    have hc := usefOutEq [188845, 97619] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨11, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188845, 97619] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl72 : ¬ a 94421 = true ∨ ¬ a 47760 = true := by
    have hc := usefOutEq [188843, 95521] (by
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨10, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188843, 95521] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl73 : ¬ a 94420 = true := by
    have hc := usefOutEq [188841] (by
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188841] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl74 : ¬ a 94419 = true := by
    have hc := usefOutEq [188839] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188839] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl75 : ¬ a 94418 = true := by
    have hc := usefOutEq [188837] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188837] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl76 : ¬ a 94417 = true := by
    have hc := usefOutEq [188835] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188835] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl77 : ¬ a 94416 = true := by
    have hc := usefOutEq [188833] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188833] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl78 : ¬ a 94415 = true := by
    have hc := usefOutEq [188831] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188831] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl79 : ¬ a 94414 = true := by
    have hc := usefOutEq [188829] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188829] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl80 : ¬ a 94413 = true := by
    have hc := usefOutEq [188827] (by
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188827] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl81 : ¬ a 94412 = true := by
    have hc := usefOutEq [188825] (by
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188825] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl82 : ¬ a 94411 = true := by
    have hc := usefOutEq [188823] (by
      refine List.mem_flatMap.mpr ⟨518, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨0, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([188823] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl83 : ¬ a 45117 = true ∨ ¬ a 92325 = true := by
    have hc := usefSrcEq [90235, 184651] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90235, 184651] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl84 : ¬ a 45117 = true ∨ a 92867 = true := by
    have hc := usefSrcEq [90235, 185734] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90235, 185734] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl85 : ¬ a 45116 = true ∨ ¬ a 92828 = true := by
    have hc := usefSrcEq [90233, 185657] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90233, 185657] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl86 : ¬ a 45116 = true ∨ a 93086 = true := by
    have hc := usefSrcEq [90233, 186172] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨773, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90233, 186172] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl87 : ¬ a 45115 = true ∨ ¬ a 92828 = true := by
    have hc := usefSrcEq [90231, 185657] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90231, 185657] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl88 : ¬ a 45115 = true ∨ a 92963 = true := by
    have hc := usefSrcEq [90231, 185926] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨650, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90231, 185926] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl89 : ¬ a 45114 = true ∨ ¬ a 92828 = true := by
    have hc := usefSrcEq [90229, 185657] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90229, 185657] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl90 : ¬ a 45114 = true ∨ a 92894 = true := by
    have hc := usefSrcEq [90229, 185788] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90229, 185788] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl91 : ¬ a 45113 = true ∨ ¬ a 92828 = true := by
    have hc := usefSrcEq [90227, 185657] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90227, 185657] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl92 : ¬ a 45113 = true ∨ a 92867 = true := by
    have hc := usefSrcEq [90227, 185734] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90227, 185734] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl93 : ¬ a 45112 = true ∨ ¬ a 92828 = true := by
    have hc := usefSrcEq [90225, 185657] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90225, 185657] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl94 : ¬ a 45112 = true ∨ a 92875 = true := by
    have hc := usefSrcEq [90225, 185750] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨562, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90225, 185750] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl95 : ¬ a 45111 = true ∨ ¬ a 92828 = true := by
    have hc := usefSrcEq [90223, 185657] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90223, 185657] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl96 : ¬ a 45111 = true ∨ a 92867 = true := by
    have hc := usefSrcEq [90223, 185734] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90223, 185734] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl97 : ¬ a 45110 = true ∨ ¬ a 92828 = true := by
    have hc := usefSrcEq [90221, 185657] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90221, 185657] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl98 : ¬ a 45110 = true ∨ a 92894 = true := by
    have hc := usefSrcEq [90221, 185788] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90221, 185788] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl99 : ¬ a 45109 = true ∨ ¬ a 92325 = true := by
    have hc := usefSrcEq [90219, 184651] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90219, 184651] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl100 : ¬ a 45109 = true ∨ a 92867 = true := by
    have hc := usefSrcEq [90219, 185734] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90219, 185734] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl101 : ¬ a 45108 = true ∨ ¬ a 92831 = true := by
    have hc := usefSrcEq [90217, 185663] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨518, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨0, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90217, 185663] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl102 : ¬ a 45108 = true ∨ a 92894 = true := by
    have hc := usefSrcEq [90217, 185788] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨0, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([90217, 185788] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl103 : ¬ a 29395 = true ∨ ¬ a 45130 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90261, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨22, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90261, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl104 : ¬ a 29395 = true ∨ ¬ a 45129 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90259, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨21, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90259, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl105 : ¬ a 29395 = true ∨ ¬ a 45128 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90257, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨20, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90257, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl106 : ¬ a 29395 = true ∨ ¬ a 45127 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90255, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨19, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90255, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl107 : ¬ a 29395 = true ∨ ¬ a 45126 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90253, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨18, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90253, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl108 : ¬ a 29395 = true ∨ ¬ a 45125 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90251, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨17, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90251, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl109 : ¬ a 29395 = true ∨ ¬ a 45124 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90249, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨16, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90249, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl110 : ¬ a 29395 = true ∨ ¬ a 45123 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90247, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨15, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90247, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl111 : ¬ a 29395 = true ∨ ¬ a 45122 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90245, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨14, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90245, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl112 : ¬ a 29395 = true ∨ ¬ a 45121 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90243, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨13, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90243, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl113 : ¬ a 29395 = true ∨ ¬ a 45120 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90241, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨12, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90241, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl114 : ¬ a 29395 = true ∨ ¬ a 45119 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90239, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨11, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90239, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl115 : ¬ a 29395 = true ∨ ¬ a 45118 = true ∨ a 123783 = true := by
    have hc := usefOrd [58791, 90237, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨22, by decide, ?_⟩
      exact List.mem_map.mpr ⟨10, by decide, rfl⟩)
    change ∃ l ∈ ([58791, 90237, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl116 : ¬ a 29383 = true ∨ ¬ a 45118 = true ∨ a 123783 = true := by
    have hc := usefOrd [58767, 90237, 247566] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨10, by decide, ?_⟩
      exact List.mem_map.mpr ⟨10, by decide, rfl⟩)
    change ∃ l ∈ ([58767, 90237, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl117 : ¬ a 29382 = true ∨ ¬ a 76590 = true := by
    have hc := usefSrcEq [58765, 153181] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58765, 153181] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl118 : ¬ a 29382 = true ∨ a 77132 = true := by
    have hc := usefSrcEq [58765, 154264] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58765, 154264] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl119 : ¬ a 29381 = true ∨ ¬ a 77093 = true := by
    have hc := usefSrcEq [58763, 154187] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58763, 154187] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl120 : ¬ a 29381 = true ∨ a 77351 = true := by
    have hc := usefSrcEq [58763, 154702] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨773, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58763, 154702] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl121 : ¬ a 29380 = true ∨ ¬ a 77093 = true := by
    have hc := usefSrcEq [58761, 154187] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58761, 154187] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl122 : ¬ a 29380 = true ∨ a 77228 = true := by
    have hc := usefSrcEq [58761, 154456] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨650, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58761, 154456] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl123 : ¬ a 29379 = true ∨ ¬ a 77093 = true := by
    have hc := usefSrcEq [58759, 154187] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58759, 154187] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl124 : ¬ a 29379 = true ∨ a 77159 = true := by
    have hc := usefSrcEq [58759, 154318] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58759, 154318] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl125 : ¬ a 29378 = true ∨ ¬ a 77093 = true := by
    have hc := usefSrcEq [58757, 154187] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58757, 154187] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl126 : ¬ a 29378 = true ∨ a 77132 = true := by
    have hc := usefSrcEq [58757, 154264] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58757, 154264] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl127 : ¬ a 29377 = true ∨ ¬ a 77093 = true := by
    have hc := usefSrcEq [58755, 154187] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58755, 154187] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl128 : ¬ a 29377 = true ∨ a 77140 = true := by
    have hc := usefSrcEq [58755, 154280] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨562, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58755, 154280] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl129 : ¬ a 29376 = true ∨ ¬ a 77093 = true := by
    have hc := usefSrcEq [58753, 154187] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58753, 154187] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl130 : ¬ a 29376 = true ∨ a 77132 = true := by
    have hc := usefSrcEq [58753, 154264] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58753, 154264] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl131 : ¬ a 29375 = true ∨ ¬ a 77093 = true := by
    have hc := usefSrcEq [58751, 154187] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58751, 154187] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl132 : ¬ a 29375 = true ∨ a 77159 = true := by
    have hc := usefSrcEq [58751, 154318] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58751, 154318] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl133 : ¬ a 29374 = true ∨ ¬ a 76590 = true := by
    have hc := usefSrcEq [58749, 153181] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58749, 153181] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl134 : ¬ a 29374 = true ∨ a 77132 = true := by
    have hc := usefSrcEq [58749, 154264] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58749, 154264] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl135 : ¬ a 29373 = true ∨ ¬ a 77096 = true := by
    have hc := usefSrcEq [58747, 154193] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨518, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨0, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58747, 154193] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl136 : ¬ a 29373 = true ∨ a 77159 = true := by
    have hc := usefSrcEq [58747, 154318] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨0, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([58747, 154318] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl137 : ¬ a 13640 = true ∨ a 61397 = true := by
    have hc := usefGate [27281, 122794] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27281, 122794] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl138 : ¬ a 13639 = true ∨ a 61397 = true ∨ ¬ a 92867 = true := by
    have hc := usefGate [27279, 122794, 185735] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 122794, 185735] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl139 : ¬ a 13639 = true ∨ a 61397 = true ∨ ¬ a 77132 = true := by
    have hc := usefGate [27279, 122794, 154265] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 122794, 154265] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl140 : ¬ a 13639 = true ∨ a 61405 = true ∨ ¬ a 92875 = true := by
    have hc := usefGate [27279, 122810, 185751] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨562, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 122810, 185751] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl141 : ¬ a 13639 = true ∨ a 61405 = true ∨ ¬ a 77140 = true := by
    have hc := usefGate [27279, 122810, 154281] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨562, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 122810, 154281] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl142 : ¬ a 13639 = true ∨ a 61424 = true ∨ ¬ a 92894 = true := by
    have hc := usefGate [27279, 122848, 185789] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 122848, 185789] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl143 : ¬ a 13639 = true ∨ a 61424 = true ∨ ¬ a 77159 = true := by
    have hc := usefGate [27279, 122848, 154319] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨581, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 122848, 154319] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl144 : ¬ a 13639 = true ∨ a 61493 = true ∨ ¬ a 92963 = true := by
    have hc := usefGate [27279, 122986, 185927] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨650, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 122986, 185927] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl145 : ¬ a 13639 = true ∨ a 61493 = true ∨ ¬ a 77228 = true := by
    have hc := usefGate [27279, 122986, 154457] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨650, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 122986, 154457] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl146 : ¬ a 13639 = true ∨ a 61616 = true ∨ ¬ a 93086 = true := by
    have hc := usefGate [27279, 123232, 186173] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨773, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 123232, 186173] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl147 : ¬ a 13639 = true ∨ a 61616 = true ∨ ¬ a 77351 = true := by
    have hc := usefGate [27279, 123232, 154703] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨773, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27279, 123232, 154703] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl148 : ¬ a 13638 = true ∨ ¬ a 61361 = true ∨ a 77096 = true := by
    have hc := usefGate [27277, 122723, 154192] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨518, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27277, 122723, 154192] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl149 : ¬ a 13638 = true ∨ ¬ a 61361 = true ∨ a 92831 = true := by
    have hc := usefGate [27277, 122723, 185662] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨518, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27277, 122723, 185662] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl150 : ¬ a 13638 = true ∨ ¬ a 61358 = true ∨ a 77093 = true := by
    have hc := usefGate [27277, 122717, 154186] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27277, 122717, 154186] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl151 : ¬ a 13638 = true ∨ ¬ a 61358 = true ∨ a 92828 = true := by
    have hc := usefGate [27277, 122717, 185656] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨515, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27277, 122717, 185656] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl152 : ¬ a 13638 = true ∨ ¬ a 60855 = true ∨ a 76590 = true := by
    have hc := usefGate [27277, 121711, 153180] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27277, 121711, 153180] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl153 : ¬ a 13638 = true ∨ ¬ a 60855 = true ∨ a 92325 = true := by
    have hc := usefGate [27277, 121711, 184650] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([27277, 121711, 184650] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl154 : ¬ a 12591 = true ∨ a 60348 = true := by
    have hc := usefGate [25183, 120696] (by
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([25183, 120696] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl155 : ¬ a 11542 = true ∨ a 59299 = true := by
    have hc := usefGate [23085, 118598] (by
      refine List.mem_flatMap.mpr ⟨11, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([23085, 118598] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl156 : ¬ a 10493 = true ∨ a 58250 = true := by
    have hc := usefGate [20987, 116500] (by
      refine List.mem_flatMap.mpr ⟨10, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([20987, 116500] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl157 : ¬ a 9444 = true ∨ a 57201 = true := by
    have hc := usefGate [18889, 114402] (by
      refine List.mem_flatMap.mpr ⟨9, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([18889, 114402] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl158 : ¬ a 8395 = true ∨ a 56152 = true := by
    have hc := usefGate [16791, 112304] (by
      refine List.mem_flatMap.mpr ⟨8, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([16791, 112304] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl159 : ¬ a 7346 = true ∨ a 55103 = true := by
    have hc := usefGate [14693, 110206] (by
      refine List.mem_flatMap.mpr ⟨7, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([14693, 110206] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl160 : ¬ a 6297 = true ∨ a 54054 = true := by
    have hc := usefGate [12595, 108108] (by
      refine List.mem_flatMap.mpr ⟨6, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([12595, 108108] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl161 : ¬ a 5248 = true ∨ a 53005 = true := by
    have hc := usefGate [10497, 106010] (by
      refine List.mem_flatMap.mpr ⟨5, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([10497, 106010] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl162 : ¬ a 4199 = true ∨ a 51956 = true := by
    have hc := usefGate [8399, 103912] (by
      refine List.mem_flatMap.mpr ⟨4, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([8399, 103912] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl163 : ¬ a 3150 = true ∨ a 50907 = true := by
    have hc := usefGate [6301, 101814] (by
      refine List.mem_flatMap.mpr ⟨3, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([6301, 101814] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl164 : ¬ a 2101 = true ∨ a 49858 = true := by
    have hc := usefGate [4203, 99716] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([4203, 99716] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl165 : ¬ a 1052 = true ∨ a 48809 = true := by
    have hc := usefGate [2105, 97618] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([2105, 97618] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl166 : ¬ a 3 = true ∨ a 47760 = true := by
    have hc := usefGate [7, 95520] (by
      refine List.mem_flatMap.mpr ⟨0, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨554, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([7, 95520] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl167 : a 13638 = true ∨ a 13639 = true ∨ a 13640 = true := by
    have hc := usefOp [27276, 27278, 27280] (by
      exact List.mem_map.mpr ⟨13, by decide, rfl⟩)
    change ∃ l ∈ ([27276, 27278, 27280] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl168 : a 29373 = true ∨ a 29374 = true ∨ a 29375 = true ∨ a 29376 = true ∨ a 29377 = true ∨ a 29378 = true ∨ a 29379 = true ∨ a 29380 = true ∨ a 29381 = true ∨ a 29382 = true ∨ a 29383 = true ∨ a 29384 = true ∨ a 29385 = true ∨ a 29386 = true ∨ a 29387 = true ∨ a 29388 = true ∨ a 29389 = true ∨ a 29390 = true ∨ a 29391 = true ∨ a 29392 = true ∨ a 29393 = true ∨ a 29394 = true ∨ a 29395 = true ∨ a 29396 = true := by
    have hc := usefSrcAlo [58746, 58748, 58750, 58752, 58754, 58756, 58758, 58760, 58762, 58764, 58766, 58768, 58770, 58772, 58774, 58776, 58778, 58780, 58782, 58784, 58786, 58788, 58790, 58792] (by
      refine List.mem_flatMap.mpr ⟨1, by decide, ?_⟩
      exact List.mem_map.mpr ⟨13, by decide, rfl⟩)
    change ∃ l ∈ ([58746, 58748, 58750, 58752, 58754, 58756, 58758, 58760, 58762, 58764, 58766, 58768, 58770, 58772, 58774, 58776, 58778, 58780, 58782, 58784, 58786, 58788, 58790, 58792] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl169 : a 29395 = true ∨ a 45130 = true ∨ a 122734 = true := by
    have hc := usefUsed [58790, 90260, 245468] (by
      exact List.mem_map.mpr ⟨12, by decide, rfl⟩)
    change ∃ l ∈ ([58790, 90260, 245468] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl170 : a 45108 = true ∨ a 45109 = true ∨ a 45110 = true ∨ a 45111 = true ∨ a 45112 = true ∨ a 45113 = true ∨ a 45114 = true ∨ a 45115 = true ∨ a 45116 = true ∨ a 45117 = true ∨ a 45118 = true ∨ a 45119 = true ∨ a 45120 = true ∨ a 45121 = true ∨ a 45122 = true ∨ a 45123 = true ∨ a 45124 = true ∨ a 45125 = true ∨ a 45126 = true ∨ a 45127 = true ∨ a 45128 = true ∨ a 45129 = true ∨ a 45130 = true ∨ a 45131 = true := by
    have hc := usefSrcAlo [90216, 90218, 90220, 90222, 90224, 90226, 90228, 90230, 90232, 90234, 90236, 90238, 90240, 90242, 90244, 90246, 90248, 90250, 90252, 90254, 90256, 90258, 90260, 90262] (by
      refine List.mem_flatMap.mpr ⟨2, by decide, ?_⟩
      exact List.mem_map.mpr ⟨13, by decide, rfl⟩)
    change ∃ l ∈ ([90216, 90218, 90220, 90222, 90224, 90226, 90228, 90230, 90232, 90234, 90236, 90238, 90240, 90242, 90244, 90246, 90248, 90250, 90252, 90254, 90256, 90258, 90260, 90262] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl171 : a 94411 = true ∨ a 94412 = true ∨ a 94413 = true ∨ a 94414 = true ∨ a 94415 = true ∨ a 94416 = true ∨ a 94417 = true ∨ a 94418 = true ∨ a 94419 = true ∨ a 94420 = true ∨ a 94421 = true ∨ a 94422 = true ∨ a 94423 = true ∨ a 94424 = true ∨ a 94425 = true ∨ a 94426 = true ∨ a 94427 = true ∨ a 94428 = true ∨ a 94429 = true ∨ a 94430 = true ∨ a 94431 = true ∨ a 94432 = true ∨ a 94433 = true ∨ a 94434 = true ∨ a 94435 = true := by
    have hc := usefOutAlo [188822, 188824, 188826, 188828, 188830, 188832, 188834, 188836, 188838, 188840, 188842, 188844, 188846, 188848, 188850, 188852, 188854, 188856, 188858, 188860, 188862, 188864, 188866, 188868, 188870] (by
      decide)
    change ∃ l ∈ ([188822, 188824, 188826, 188828, 188830, 188832, 188834, 188836, 188838, 188840, 188842, 188844, 188846, 188848, 188850, 188852, 188854, 188856, 188858, 188860, 188862, 188864, 188866, 188868, 188870] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl172 : a 94434 = true ∨ a 123783 = true := by
    have hc := usefOut [188868, 247566] (by
      decide)
    change ∃ l ∈ ([188868, 247566] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl173 : a 123783 = true ∨ ¬ a 45131 = true := by
    have hc := usefPad [247566, 90263] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([247566, 90263] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl174 : a 123783 = true ∨ ¬ a 29396 = true := by
    have hc := usefPad [247566, 58793] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([247566, 58793] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have cl175 : a 123783 = true ∨ ¬ a 13640 = true := by
    have hc := usefPad [247566, 27281] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      decide)
    change ∃ l ∈ ([247566, 27281] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true at hc
    simpa using hc
  have nonpad : ¬ a 123783 = true := by
    by_contra bad
    have assume0 : a 123783 = true := by simpa only [not_not] using bad
    have step0 : ¬ a 94411 = true := cl82
    have step1 : ¬ a 94412 = true := cl81
    have step2 : ¬ a 94413 = true := cl80
    have step3 : ¬ a 94414 = true := cl79
    have step4 : ¬ a 94415 = true := cl78
    have step5 : ¬ a 94416 = true := cl77
    have step6 : ¬ a 94417 = true := cl76
    have step7 : ¬ a 94418 = true := cl75
    have step8 : ¬ a 94419 = true := cl74
    have step9 : ¬ a 94420 = true := cl73
    have step10 : a 122734 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl1
    have step11 : a 121685 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step10)) (fun h1 => h1)) cl5
    have step12 : a 120636 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step11)) (fun h1 => h1)) cl9
    have step13 : a 119587 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step12)) (fun h1 => h1)) cl13
    have step14 : a 118538 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step13)) (fun h1 => h1)) cl17
    have step15 : a 117489 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step14)) (fun h1 => h1)) cl21
    have step16 : a 116440 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step15)) (fun h1 => h1)) cl25
    have step17 : a 115391 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step16)) (fun h1 => h1)) cl29
    have step18 : a 114342 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step17)) (fun h1 => h1)) cl33
    have step19 : a 113293 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step18)) (fun h1 => h1)) cl37
    have step20 : a 112244 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step19)) (fun h1 => h1)) cl41
    have step21 : a 111195 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step20)) (fun h1 => h1)) cl45
    have step22 : a 1052 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step21)) (fun h1 => h1)) cl48
    have step23 : a 48809 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step22)) (fun h1 => h1)) cl165
    have step24 : ¬ a 94422 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step23))) cl71
    have step25 : a 2101 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step20)) (fun h1 => h1)) cl44
    have step26 : a 49858 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step25)) (fun h1 => h1)) cl164
    have step27 : ¬ a 94423 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step26))) cl70
    have step28 : a 3150 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step19)) (fun h1 => h1)) cl40
    have step29 : a 50907 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step28)) (fun h1 => h1)) cl163
    have step30 : ¬ a 94424 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step29))) cl69
    have step31 : a 4199 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step18)) (fun h1 => h1)) cl36
    have step32 : a 51956 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step31)) (fun h1 => h1)) cl162
    have step33 : ¬ a 94425 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step32))) cl68
    have step34 : a 5248 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step17)) (fun h1 => h1)) cl32
    have step35 : a 53005 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step34)) (fun h1 => h1)) cl161
    have step36 : ¬ a 94426 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step35))) cl67
    have step37 : a 6297 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step16)) (fun h1 => h1)) cl28
    have step38 : a 54054 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step37)) (fun h1 => h1)) cl160
    have step39 : ¬ a 94427 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step38))) cl66
    have step40 : a 7346 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step15)) (fun h1 => h1)) cl24
    have step41 : a 55103 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step40)) (fun h1 => h1)) cl159
    have step42 : ¬ a 94428 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step41))) cl65
    have step43 : a 8395 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step14)) (fun h1 => h1)) cl20
    have step44 : a 56152 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step43)) (fun h1 => h1)) cl158
    have step45 : ¬ a 94429 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step44))) cl64
    have step46 : a 9444 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step13)) (fun h1 => h1)) cl16
    have step47 : a 57201 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step46)) (fun h1 => h1)) cl157
    have step48 : ¬ a 94430 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step47))) cl63
    have step49 : a 10493 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step12)) (fun h1 => h1)) cl12
    have step50 : a 58250 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step49)) (fun h1 => h1)) cl156
    have step51 : ¬ a 94431 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step50))) cl62
    have step52 : a 11542 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step11)) (fun h1 => h1)) cl8
    have step53 : a 59299 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step52)) (fun h1 => h1)) cl155
    have step54 : ¬ a 94432 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step53))) cl61
    have step55 : a 12591 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step10)) (fun h1 => h1)) cl4
    have step56 : a 60348 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step55)) (fun h1 => h1)) cl154
    have step57 : ¬ a 94433 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step56))) cl60
    have step58 : a 13640 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl0
    have step59 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step58)) (fun h1 => h1)) cl137
    have step60 : ¬ a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (h1 step59))) cl56
    have step61 : ¬ a 94435 = true := cl51
    have step62 : a 94421 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step1 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step2 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step3 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step4 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step5 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step6 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step7 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step8 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step9 h9)) (fun hh => Or.elim hh (fun h10 => h10) (fun hh => Or.elim hh (fun h11 => False.elim (step24 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (step27 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (step30 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (step33 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (step36 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (step39 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (step42 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (step45 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (step48 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (step51 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (step54 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step57 h22)) (fun hh => Or.elim hh (fun h23 => False.elim (step60 h23)) (fun h24 => False.elim (step61 h24)))))))))))))))))))))))))) cl171
    have step63 : a 110146 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step21)) (fun h1 => h1)) cl49
    have step64 : a 3 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step63)) (fun h1 => h1)) cl50
    have step65 : a 47760 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step64)) (fun h1 => h1)) cl166
    exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step62)) (fun h1 => False.elim (h1 step65))) cl72
  have binary : a 13638 = true ∨ a 13639 = true := by
    by_contra bad
    have assume0 : ¬ a 13638 = true := fun h => bad (Or.inl h)
    have assume1 : ¬ a 13639 = true := fun h => bad (Or.inr h)
    have step0 : ¬ a 123783 = true := nonpad
    have step1 : a 13640 = true := (fun hh => Or.elim hh (fun h0 => False.elim (assume0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (assume1 h1)) (fun h2 => h2))) cl167
    exact (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun h1 => False.elim (h1 step1))) cl175
  rcases binary with choice | choice
  ·
    have raw0_1_0 : ¬ a 29373 = true := by
      by_contra bad
      have assume0 : a 29373 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 77096 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl135
      have step3 : ¬ a 61361 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl148
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl59
    have raw0_1_1 : ¬ a 29374 = true := by
      by_contra bad
      have assume0 : a 29374 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 76590 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl133
      have step3 : ¬ a 60855 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl152
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl57
    have raw0_1_2 : ¬ a 29375 = true := by
      by_contra bad
      have assume0 : a 29375 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 77093 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl131
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl150
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_1_3 : ¬ a 29376 = true := by
      by_contra bad
      have assume0 : a 29376 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 77093 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl129
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl150
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_1_4 : ¬ a 29377 = true := by
      by_contra bad
      have assume0 : a 29377 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 77093 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl127
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl150
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_1_5 : ¬ a 29378 = true := by
      by_contra bad
      have assume0 : a 29378 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 77093 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl125
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl150
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_1_6 : ¬ a 29379 = true := by
      by_contra bad
      have assume0 : a 29379 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 77093 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl123
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl150
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_1_7 : ¬ a 29380 = true := by
      by_contra bad
      have assume0 : a 29380 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 77093 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl121
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl150
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_1_8 : ¬ a 29381 = true := by
      by_contra bad
      have assume0 : a 29381 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 77093 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl119
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl150
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_1_9 : ¬ a 29382 = true := by
      by_contra bad
      have assume0 : a 29382 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 76590 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl117
      have step3 : ¬ a 60855 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl152
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl57
    have raw0_2_0 : ¬ a 45108 = true := by
      by_contra bad
      have assume0 : a 45108 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92831 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl101
      have step3 : ¬ a 61361 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl149
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl59
    have raw0_2_1 : ¬ a 45109 = true := by
      by_contra bad
      have assume0 : a 45109 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92325 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl99
      have step3 : ¬ a 60855 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl153
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl57
    have raw0_2_2 : ¬ a 45110 = true := by
      by_contra bad
      have assume0 : a 45110 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92828 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl97
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl151
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_2_3 : ¬ a 45111 = true := by
      by_contra bad
      have assume0 : a 45111 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92828 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl95
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl151
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_2_4 : ¬ a 45112 = true := by
      by_contra bad
      have assume0 : a 45112 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92828 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl93
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl151
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_2_5 : ¬ a 45113 = true := by
      by_contra bad
      have assume0 : a 45113 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92828 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl91
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl151
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_2_6 : ¬ a 45114 = true := by
      by_contra bad
      have assume0 : a 45114 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92828 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl89
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl151
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_2_7 : ¬ a 45115 = true := by
      by_contra bad
      have assume0 : a 45115 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92828 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl87
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl151
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_2_8 : ¬ a 45116 = true := by
      by_contra bad
      have assume0 : a 45116 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92828 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl85
      have step3 : ¬ a 61358 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl151
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl58
    have raw0_2_9 : ¬ a 45117 = true := by
      by_contra bad
      have assume0 : a 45117 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : ¬ a 92325 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl83
      have step3 : ¬ a 60855 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step2 h2)))) cl153
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (step3 h1))) cl57
    have prev0 : ¬ a 122734 = true := by
      by_contra bad
      have assume0 : a 122734 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 29373 = true := raw0_1_0
      have step1 : ¬ a 29374 = true := raw0_1_1
      have step2 : ¬ a 29375 = true := raw0_1_2
      have step3 : ¬ a 29376 = true := raw0_1_3
      have step4 : ¬ a 29377 = true := raw0_1_4
      have step5 : ¬ a 29378 = true := raw0_1_5
      have step6 : ¬ a 29379 = true := raw0_1_6
      have step7 : ¬ a 29380 = true := raw0_1_7
      have step8 : ¬ a 29381 = true := raw0_1_8
      have step9 : ¬ a 29382 = true := raw0_1_9
      have step10 : a 121685 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl5
      have step11 : a 120636 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step10)) (fun h1 => h1)) cl9
      have step12 : a 119587 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step11)) (fun h1 => h1)) cl13
      have step13 : a 118538 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step12)) (fun h1 => h1)) cl17
      have step14 : a 117489 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step13)) (fun h1 => h1)) cl21
      have step15 : a 116440 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step14)) (fun h1 => h1)) cl25
      have step16 : a 115391 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step15)) (fun h1 => h1)) cl29
      have step17 : a 114342 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step16)) (fun h1 => h1)) cl33
      have step18 : a 113293 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step17)) (fun h1 => h1)) cl37
      have step19 : a 112244 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step18)) (fun h1 => h1)) cl41
      have step20 : a 111195 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step19)) (fun h1 => h1)) cl45
      have step21 : ¬ a 29384 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step20)) (fun h1 => h1)) cl47
      have step22 : ¬ a 29385 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step19)) (fun h1 => h1)) cl43
      have step23 : ¬ a 29386 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step18)) (fun h1 => h1)) cl39
      have step24 : ¬ a 29387 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step17)) (fun h1 => h1)) cl35
      have step25 : ¬ a 29388 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step16)) (fun h1 => h1)) cl31
      have step26 : ¬ a 29389 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step15)) (fun h1 => h1)) cl27
      have step27 : ¬ a 29390 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step14)) (fun h1 => h1)) cl23
      have step28 : ¬ a 29391 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step13)) (fun h1 => h1)) cl19
      have step29 : ¬ a 29392 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step12)) (fun h1 => h1)) cl15
      have step30 : ¬ a 29393 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step11)) (fun h1 => h1)) cl11
      have step31 : ¬ a 29394 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step10)) (fun h1 => h1)) cl7
      have step32 : ¬ a 29395 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl3
      have step33 : ¬ a 123783 = true := nonpad
      have step34 : ¬ a 29396 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step33 h0)) (fun h1 => h1)) cl174
      have step35 : a 29383 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step1 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step2 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step3 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step4 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step5 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step6 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step7 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step8 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step9 h9)) (fun hh => Or.elim hh (fun h10 => h10) (fun hh => Or.elim hh (fun h11 => False.elim (step21 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (step22 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (step23 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (step24 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (step25 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (step26 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (step27 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (step28 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (step29 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (step30 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (step31 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step32 h22)) (fun h23 => False.elim (step34 h23))))))))))))))))))))))))) cl168
      have step36 : ¬ a 45108 = true := raw0_2_0
      have step37 : ¬ a 45109 = true := raw0_2_1
      have step38 : ¬ a 45110 = true := raw0_2_2
      have step39 : ¬ a 45111 = true := raw0_2_3
      have step40 : ¬ a 45112 = true := raw0_2_4
      have step41 : ¬ a 45113 = true := raw0_2_5
      have step42 : ¬ a 45114 = true := raw0_2_6
      have step43 : ¬ a 45115 = true := raw0_2_7
      have step44 : ¬ a 45116 = true := raw0_2_8
      have step45 : ¬ a 45117 = true := raw0_2_9
      have step46 : ¬ a 45119 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step20)) (fun h1 => h1)) cl46
      have step47 : ¬ a 45120 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step19)) (fun h1 => h1)) cl42
      have step48 : ¬ a 45121 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step18)) (fun h1 => h1)) cl38
      have step49 : ¬ a 45122 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step17)) (fun h1 => h1)) cl34
      have step50 : ¬ a 45123 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step16)) (fun h1 => h1)) cl30
      have step51 : ¬ a 45124 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step15)) (fun h1 => h1)) cl26
      have step52 : ¬ a 45125 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step14)) (fun h1 => h1)) cl22
      have step53 : ¬ a 45126 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step13)) (fun h1 => h1)) cl18
      have step54 : ¬ a 45127 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step12)) (fun h1 => h1)) cl14
      have step55 : ¬ a 45128 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step11)) (fun h1 => h1)) cl10
      have step56 : ¬ a 45129 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step10)) (fun h1 => h1)) cl6
      have step57 : ¬ a 45130 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl2
      have step58 : ¬ a 45131 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step33 h0)) (fun h1 => h1)) cl173
      have step59 : a 45118 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step36 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step37 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step38 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step39 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step40 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step41 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step42 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step43 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step44 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step45 h9)) (fun hh => Or.elim hh (fun h10 => h10) (fun hh => Or.elim hh (fun h11 => False.elim (step46 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (step47 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (step48 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (step49 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (step50 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (step51 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (step52 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (step53 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (step54 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (step55 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (step56 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step57 h22)) (fun h23 => False.elim (step58 h23))))))))))))))))))))))))) cl170
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step35)) (fun hh => Or.elim hh (fun h1 => False.elim (h1 step59)) (fun h2 => False.elim (step33 h2)))) cl116
    have ordered0 : ¬ a 29395 = true := by
      by_contra bad
      have assume0 : a 29395 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 45108 = true := raw0_2_0
      have step1 : ¬ a 45109 = true := raw0_2_1
      have step2 : ¬ a 45110 = true := raw0_2_2
      have step3 : ¬ a 45111 = true := raw0_2_3
      have step4 : ¬ a 45112 = true := raw0_2_4
      have step5 : ¬ a 45113 = true := raw0_2_5
      have step6 : ¬ a 45114 = true := raw0_2_6
      have step7 : ¬ a 45115 = true := raw0_2_7
      have step8 : ¬ a 45116 = true := raw0_2_8
      have step9 : ¬ a 45117 = true := raw0_2_9
      have step10 : ¬ a 123783 = true := nonpad
      have step11 : ¬ a 45118 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl115
      have step12 : ¬ a 45119 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl114
      have step13 : ¬ a 45120 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl113
      have step14 : ¬ a 45121 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl112
      have step15 : ¬ a 45122 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl111
      have step16 : ¬ a 45123 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl110
      have step17 : ¬ a 45124 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl109
      have step18 : ¬ a 45125 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl108
      have step19 : ¬ a 45126 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl107
      have step20 : ¬ a 45127 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl106
      have step21 : ¬ a 45128 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl105
      have step22 : ¬ a 45129 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl104
      have step23 : ¬ a 45130 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl103
      have step24 : ¬ a 45131 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step10 h0)) (fun h1 => h1)) cl173
      exact (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step1 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step2 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step3 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step4 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step5 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step6 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step7 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step8 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step9 h9)) (fun hh => Or.elim hh (fun h10 => False.elim (step11 h10)) (fun hh => Or.elim hh (fun h11 => False.elim (step12 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (step13 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (step14 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (step15 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (step16 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (step17 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (step18 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (step19 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (step20 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (step21 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (step22 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step23 h22)) (fun h23 => False.elim (step24 h23))))))))))))))))))))))))) cl170
    have penult0 : a 45130 = true := by
      by_contra bad
      have assume0 : ¬ a 45130 = true := fun h => bad h
      have step0 : ¬ a 29395 = true := ordered0
      have step1 : ¬ a 122734 = true := prev0
      exact (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (assume0 h1)) (fun h2 => False.elim (step1 h2)))) cl169
    have internal0 : a 29383 = true ∨ a 29384 = true ∨ a 29385 = true ∨ a 29386 = true ∨ a 29387 = true ∨ a 29388 = true ∨ a 29389 = true ∨ a 29390 = true ∨ a 29391 = true ∨ a 29392 = true ∨ a 29393 = true ∨ a 29394 = true := by
      by_contra bad
      have assume0 : ¬ a 29383 = true := fun h => bad (Or.inl h)
      have assume1 : ¬ a 29384 = true := fun h => bad (Or.inr (Or.inl h))
      have assume2 : ¬ a 29385 = true := fun h => bad (Or.inr (Or.inr (Or.inl h)))
      have assume3 : ¬ a 29386 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inl h))))
      have assume4 : ¬ a 29387 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      have assume5 : ¬ a 29388 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      have assume6 : ¬ a 29389 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      have assume7 : ¬ a 29390 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      have assume8 : ¬ a 29391 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
      have assume9 : ¬ a 29392 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
      have assume10 : ¬ a 29393 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
      have assume11 : ¬ a 29394 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))
      have step0 : ¬ a 29373 = true := raw0_1_0
      have step1 : ¬ a 29374 = true := raw0_1_1
      have step2 : ¬ a 29375 = true := raw0_1_2
      have step3 : ¬ a 29376 = true := raw0_1_3
      have step4 : ¬ a 29377 = true := raw0_1_4
      have step5 : ¬ a 29378 = true := raw0_1_5
      have step6 : ¬ a 29379 = true := raw0_1_6
      have step7 : ¬ a 29380 = true := raw0_1_7
      have step8 : ¬ a 29381 = true := raw0_1_8
      have step9 : ¬ a 29382 = true := raw0_1_9
      have step10 : ¬ a 29395 = true := ordered0
      have step11 : ¬ a 123783 = true := nonpad
      have step12 : ¬ a 29396 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step11 h0)) (fun h1 => h1)) cl174
      exact (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step1 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step2 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step3 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step4 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step5 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step6 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step7 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step8 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step9 h9)) (fun hh => Or.elim hh (fun h10 => False.elim (assume0 h10)) (fun hh => Or.elim hh (fun h11 => False.elim (assume1 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (assume2 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (assume3 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (assume4 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (assume5 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (assume6 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (assume7 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (assume8 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (assume9 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (assume10 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (assume11 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step10 h22)) (fun h23 => False.elim (step12 h23))))))))))))))))))))))))) cl168
    apply h0
    refine ⟨a, ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact ha c h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · change ∃ l ∈ ([27276] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true
      simpa using choice
    · change ∃ l ∈ ([90260] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true
      simpa using penult0
    · change ∃ l ∈ ([58766, 58768, 58770, 58772, 58774, 58776, 58778, 58780, 58782, 58784, 58786, 58788] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true
      simpa using internal0
  ·
    have raw1_1_0 : ¬ a 29373 = true := by
      by_contra bad
      have assume0 : a 29373 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77159 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl136
      have step3 : a 61424 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl143
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl54
    have raw1_1_1 : ¬ a 29374 = true := by
      by_contra bad
      have assume0 : a 29374 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77132 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl134
      have step3 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl139
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl56
    have raw1_1_2 : ¬ a 29375 = true := by
      by_contra bad
      have assume0 : a 29375 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77159 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl132
      have step3 : a 61424 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl143
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl54
    have raw1_1_3 : ¬ a 29376 = true := by
      by_contra bad
      have assume0 : a 29376 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77132 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl130
      have step3 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl139
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl56
    have raw1_1_4 : ¬ a 29377 = true := by
      by_contra bad
      have assume0 : a 29377 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77140 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl128
      have step3 : a 61405 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl141
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl55
    have raw1_1_5 : ¬ a 29378 = true := by
      by_contra bad
      have assume0 : a 29378 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77132 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl126
      have step3 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl139
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl56
    have raw1_1_6 : ¬ a 29379 = true := by
      by_contra bad
      have assume0 : a 29379 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77159 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl124
      have step3 : a 61424 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl143
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl54
    have raw1_1_7 : ¬ a 29380 = true := by
      by_contra bad
      have assume0 : a 29380 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77228 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl122
      have step3 : a 61493 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl145
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl53
    have raw1_1_8 : ¬ a 29381 = true := by
      by_contra bad
      have assume0 : a 29381 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77351 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl120
      have step3 : a 61616 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl147
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl52
    have raw1_1_9 : ¬ a 29382 = true := by
      by_contra bad
      have assume0 : a 29382 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 77132 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl118
      have step3 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl139
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl56
    have raw1_2_0 : ¬ a 45108 = true := by
      by_contra bad
      have assume0 : a 45108 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92894 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl102
      have step3 : a 61424 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl142
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl54
    have raw1_2_1 : ¬ a 45109 = true := by
      by_contra bad
      have assume0 : a 45109 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92867 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl100
      have step3 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl138
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl56
    have raw1_2_2 : ¬ a 45110 = true := by
      by_contra bad
      have assume0 : a 45110 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92894 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl98
      have step3 : a 61424 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl142
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl54
    have raw1_2_3 : ¬ a 45111 = true := by
      by_contra bad
      have assume0 : a 45111 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92867 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl96
      have step3 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl138
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl56
    have raw1_2_4 : ¬ a 45112 = true := by
      by_contra bad
      have assume0 : a 45112 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92875 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl94
      have step3 : a 61405 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl140
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl55
    have raw1_2_5 : ¬ a 45113 = true := by
      by_contra bad
      have assume0 : a 45113 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92867 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl92
      have step3 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl138
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl56
    have raw1_2_6 : ¬ a 45114 = true := by
      by_contra bad
      have assume0 : a 45114 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92894 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl90
      have step3 : a 61424 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl142
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl54
    have raw1_2_7 : ¬ a 45115 = true := by
      by_contra bad
      have assume0 : a 45115 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92963 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl88
      have step3 : a 61493 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl144
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl53
    have raw1_2_8 : ¬ a 45116 = true := by
      by_contra bad
      have assume0 : a 45116 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 93086 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl86
      have step3 : a 61616 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl146
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl52
    have raw1_2_9 : ¬ a 45117 = true := by
      by_contra bad
      have assume0 : a 45117 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 123783 = true := nonpad
      have step1 : a 94434 = true := (fun hh => Or.elim hh (fun h0 => h0) (fun h1 => False.elim (step0 h1))) cl172
      have step2 : a 92867 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl84
      have step3 : a 61397 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 choice)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (h2 step2)))) cl138
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step1)) (fun h1 => False.elim (h1 step3))) cl56
    have prev1 : ¬ a 122734 = true := by
      by_contra bad
      have assume0 : a 122734 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 29373 = true := raw1_1_0
      have step1 : ¬ a 29374 = true := raw1_1_1
      have step2 : ¬ a 29375 = true := raw1_1_2
      have step3 : ¬ a 29376 = true := raw1_1_3
      have step4 : ¬ a 29377 = true := raw1_1_4
      have step5 : ¬ a 29378 = true := raw1_1_5
      have step6 : ¬ a 29379 = true := raw1_1_6
      have step7 : ¬ a 29380 = true := raw1_1_7
      have step8 : ¬ a 29381 = true := raw1_1_8
      have step9 : ¬ a 29382 = true := raw1_1_9
      have step10 : a 121685 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl5
      have step11 : a 120636 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step10)) (fun h1 => h1)) cl9
      have step12 : a 119587 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step11)) (fun h1 => h1)) cl13
      have step13 : a 118538 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step12)) (fun h1 => h1)) cl17
      have step14 : a 117489 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step13)) (fun h1 => h1)) cl21
      have step15 : a 116440 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step14)) (fun h1 => h1)) cl25
      have step16 : a 115391 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step15)) (fun h1 => h1)) cl29
      have step17 : a 114342 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step16)) (fun h1 => h1)) cl33
      have step18 : a 113293 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step17)) (fun h1 => h1)) cl37
      have step19 : a 112244 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step18)) (fun h1 => h1)) cl41
      have step20 : a 111195 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step19)) (fun h1 => h1)) cl45
      have step21 : ¬ a 29384 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step20)) (fun h1 => h1)) cl47
      have step22 : ¬ a 29385 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step19)) (fun h1 => h1)) cl43
      have step23 : ¬ a 29386 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step18)) (fun h1 => h1)) cl39
      have step24 : ¬ a 29387 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step17)) (fun h1 => h1)) cl35
      have step25 : ¬ a 29388 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step16)) (fun h1 => h1)) cl31
      have step26 : ¬ a 29389 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step15)) (fun h1 => h1)) cl27
      have step27 : ¬ a 29390 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step14)) (fun h1 => h1)) cl23
      have step28 : ¬ a 29391 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step13)) (fun h1 => h1)) cl19
      have step29 : ¬ a 29392 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step12)) (fun h1 => h1)) cl15
      have step30 : ¬ a 29393 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step11)) (fun h1 => h1)) cl11
      have step31 : ¬ a 29394 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step10)) (fun h1 => h1)) cl7
      have step32 : ¬ a 29395 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl3
      have step33 : ¬ a 123783 = true := nonpad
      have step34 : ¬ a 29396 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step33 h0)) (fun h1 => h1)) cl174
      have step35 : a 29383 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step1 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step2 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step3 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step4 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step5 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step6 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step7 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step8 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step9 h9)) (fun hh => Or.elim hh (fun h10 => h10) (fun hh => Or.elim hh (fun h11 => False.elim (step21 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (step22 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (step23 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (step24 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (step25 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (step26 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (step27 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (step28 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (step29 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (step30 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (step31 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step32 h22)) (fun h23 => False.elim (step34 h23))))))))))))))))))))))))) cl168
      have step36 : ¬ a 45108 = true := raw1_2_0
      have step37 : ¬ a 45109 = true := raw1_2_1
      have step38 : ¬ a 45110 = true := raw1_2_2
      have step39 : ¬ a 45111 = true := raw1_2_3
      have step40 : ¬ a 45112 = true := raw1_2_4
      have step41 : ¬ a 45113 = true := raw1_2_5
      have step42 : ¬ a 45114 = true := raw1_2_6
      have step43 : ¬ a 45115 = true := raw1_2_7
      have step44 : ¬ a 45116 = true := raw1_2_8
      have step45 : ¬ a 45117 = true := raw1_2_9
      have step46 : ¬ a 45119 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step20)) (fun h1 => h1)) cl46
      have step47 : ¬ a 45120 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step19)) (fun h1 => h1)) cl42
      have step48 : ¬ a 45121 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step18)) (fun h1 => h1)) cl38
      have step49 : ¬ a 45122 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step17)) (fun h1 => h1)) cl34
      have step50 : ¬ a 45123 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step16)) (fun h1 => h1)) cl30
      have step51 : ¬ a 45124 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step15)) (fun h1 => h1)) cl26
      have step52 : ¬ a 45125 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step14)) (fun h1 => h1)) cl22
      have step53 : ¬ a 45126 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step13)) (fun h1 => h1)) cl18
      have step54 : ¬ a 45127 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step12)) (fun h1 => h1)) cl14
      have step55 : ¬ a 45128 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step11)) (fun h1 => h1)) cl10
      have step56 : ¬ a 45129 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 step10)) (fun h1 => h1)) cl6
      have step57 : ¬ a 45130 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun h1 => h1)) cl2
      have step58 : ¬ a 45131 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step33 h0)) (fun h1 => h1)) cl173
      have step59 : a 45118 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step36 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step37 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step38 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step39 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step40 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step41 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step42 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step43 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step44 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step45 h9)) (fun hh => Or.elim hh (fun h10 => h10) (fun hh => Or.elim hh (fun h11 => False.elim (step46 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (step47 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (step48 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (step49 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (step50 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (step51 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (step52 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (step53 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (step54 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (step55 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (step56 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step57 h22)) (fun h23 => False.elim (step58 h23))))))))))))))))))))))))) cl170
      exact (fun hh => Or.elim hh (fun h0 => False.elim (h0 step35)) (fun hh => Or.elim hh (fun h1 => False.elim (h1 step59)) (fun h2 => False.elim (step33 h2)))) cl116
    have ordered1 : ¬ a 29395 = true := by
      by_contra bad
      have assume0 : a 29395 = true := by simpa only [not_not] using bad
      have step0 : ¬ a 45108 = true := raw1_2_0
      have step1 : ¬ a 45109 = true := raw1_2_1
      have step2 : ¬ a 45110 = true := raw1_2_2
      have step3 : ¬ a 45111 = true := raw1_2_3
      have step4 : ¬ a 45112 = true := raw1_2_4
      have step5 : ¬ a 45113 = true := raw1_2_5
      have step6 : ¬ a 45114 = true := raw1_2_6
      have step7 : ¬ a 45115 = true := raw1_2_7
      have step8 : ¬ a 45116 = true := raw1_2_8
      have step9 : ¬ a 45117 = true := raw1_2_9
      have step10 : ¬ a 123783 = true := nonpad
      have step11 : ¬ a 45118 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl115
      have step12 : ¬ a 45119 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl114
      have step13 : ¬ a 45120 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl113
      have step14 : ¬ a 45121 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl112
      have step15 : ¬ a 45122 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl111
      have step16 : ¬ a 45123 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl110
      have step17 : ¬ a 45124 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl109
      have step18 : ¬ a 45125 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl108
      have step19 : ¬ a 45126 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl107
      have step20 : ¬ a 45127 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl106
      have step21 : ¬ a 45128 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl105
      have step22 : ¬ a 45129 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl104
      have step23 : ¬ a 45130 = true := (fun hh => Or.elim hh (fun h0 => False.elim (h0 assume0)) (fun hh => Or.elim hh (fun h1 => h1) (fun h2 => False.elim (step10 h2)))) cl103
      have step24 : ¬ a 45131 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step10 h0)) (fun h1 => h1)) cl173
      exact (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step1 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step2 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step3 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step4 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step5 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step6 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step7 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step8 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step9 h9)) (fun hh => Or.elim hh (fun h10 => False.elim (step11 h10)) (fun hh => Or.elim hh (fun h11 => False.elim (step12 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (step13 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (step14 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (step15 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (step16 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (step17 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (step18 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (step19 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (step20 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (step21 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (step22 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step23 h22)) (fun h23 => False.elim (step24 h23))))))))))))))))))))))))) cl170
    have penult1 : a 45130 = true := by
      by_contra bad
      have assume0 : ¬ a 45130 = true := fun h => bad h
      have step0 : ¬ a 29395 = true := ordered1
      have step1 : ¬ a 122734 = true := prev1
      exact (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (assume0 h1)) (fun h2 => False.elim (step1 h2)))) cl169
    have internal1 : a 29383 = true ∨ a 29384 = true ∨ a 29385 = true ∨ a 29386 = true ∨ a 29387 = true ∨ a 29388 = true ∨ a 29389 = true ∨ a 29390 = true ∨ a 29391 = true ∨ a 29392 = true ∨ a 29393 = true ∨ a 29394 = true := by
      by_contra bad
      have assume0 : ¬ a 29383 = true := fun h => bad (Or.inl h)
      have assume1 : ¬ a 29384 = true := fun h => bad (Or.inr (Or.inl h))
      have assume2 : ¬ a 29385 = true := fun h => bad (Or.inr (Or.inr (Or.inl h)))
      have assume3 : ¬ a 29386 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inl h))))
      have assume4 : ¬ a 29387 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      have assume5 : ¬ a 29388 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      have assume6 : ¬ a 29389 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      have assume7 : ¬ a 29390 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      have assume8 : ¬ a 29391 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
      have assume9 : ¬ a 29392 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
      have assume10 : ¬ a 29393 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
      have assume11 : ¬ a 29394 = true := fun h => bad (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))
      have step0 : ¬ a 29373 = true := raw1_1_0
      have step1 : ¬ a 29374 = true := raw1_1_1
      have step2 : ¬ a 29375 = true := raw1_1_2
      have step3 : ¬ a 29376 = true := raw1_1_3
      have step4 : ¬ a 29377 = true := raw1_1_4
      have step5 : ¬ a 29378 = true := raw1_1_5
      have step6 : ¬ a 29379 = true := raw1_1_6
      have step7 : ¬ a 29380 = true := raw1_1_7
      have step8 : ¬ a 29381 = true := raw1_1_8
      have step9 : ¬ a 29382 = true := raw1_1_9
      have step10 : ¬ a 29395 = true := ordered1
      have step11 : ¬ a 123783 = true := nonpad
      have step12 : ¬ a 29396 = true := (fun hh => Or.elim hh (fun h0 => False.elim (step11 h0)) (fun h1 => h1)) cl174
      exact (fun hh => Or.elim hh (fun h0 => False.elim (step0 h0)) (fun hh => Or.elim hh (fun h1 => False.elim (step1 h1)) (fun hh => Or.elim hh (fun h2 => False.elim (step2 h2)) (fun hh => Or.elim hh (fun h3 => False.elim (step3 h3)) (fun hh => Or.elim hh (fun h4 => False.elim (step4 h4)) (fun hh => Or.elim hh (fun h5 => False.elim (step5 h5)) (fun hh => Or.elim hh (fun h6 => False.elim (step6 h6)) (fun hh => Or.elim hh (fun h7 => False.elim (step7 h7)) (fun hh => Or.elim hh (fun h8 => False.elim (step8 h8)) (fun hh => Or.elim hh (fun h9 => False.elim (step9 h9)) (fun hh => Or.elim hh (fun h10 => False.elim (assume0 h10)) (fun hh => Or.elim hh (fun h11 => False.elim (assume1 h11)) (fun hh => Or.elim hh (fun h12 => False.elim (assume2 h12)) (fun hh => Or.elim hh (fun h13 => False.elim (assume3 h13)) (fun hh => Or.elim hh (fun h14 => False.elim (assume4 h14)) (fun hh => Or.elim hh (fun h15 => False.elim (assume5 h15)) (fun hh => Or.elim hh (fun h16 => False.elim (assume6 h16)) (fun hh => Or.elim hh (fun h17 => False.elim (assume7 h17)) (fun hh => Or.elim hh (fun h18 => False.elim (assume8 h18)) (fun hh => Or.elim hh (fun h19 => False.elim (assume9 h19)) (fun hh => Or.elim hh (fun h20 => False.elim (assume10 h20)) (fun hh => Or.elim hh (fun h21 => False.elim (assume11 h21)) (fun hh => Or.elim hh (fun h22 => False.elim (step10 h22)) (fun h23 => False.elim (step12 h23))))))))))))))))))))))))) cl168
    apply h1
    refine ⟨a, ?_⟩
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact ha c h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · change ∃ l ∈ ([27278] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true
      simpa using choice
    · change ∃ l ∈ ([90260] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true
      simpa using penult1
    · change ∃ l ∈ ([58766, 58768, 58770, 58772, 58774, 58776, 58778, 58780, 58782, 58784, 58786, 58788] : List ℕ), (a (l / 2) == (l % 2 == 0)) = true
      simpa using internal1
