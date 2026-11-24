import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_457 : ∀ E : List (Fin 3 × Fin 3), E = [(0, 1), (0, 2), (1, 2)] → ∀ τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3, (∀ e ∈ E, ∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 3 × Fin 3 → ℚ, (∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 3, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hsum e he
  subst E
  have hI (i : Fin 3) :
      ∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)),
        ¬ (f.1 ∈ ({i} : Finset (Fin 3)) ∧ f.2 ∈ ({i} : Finset (Fin 3))) := by
    fin_cases i <;> decide
  have hchoice (i a b : Fin 3)
      (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3))) :
      τ (a, b) {i} = a ∨ τ (a, b) {i} = b :=
    (hτ (a, b) hab {i} (hI i)).1
  have hnot (i a b : Fin 3)
      (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3))) :
      τ (a, b) {i} ≠ i := by
    simpa using (hτ (a, b) hab {i} (hI i)).2
  have hleft (i b : Fin 3)
      (hab : (i, b) ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3))) :
      τ (i, b) {i} = b := by
    rcases hchoice i i b hab with h | h
    · exact (hnot i i b hab h).elim
    · exact h
  have hright (i a : Fin 3)
      (hab : (a, i) ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3))) :
      τ (a, i) {i} = a := by
    rcases hchoice i a i hab with h | h
    · exact h
    · exact (hnot i a i hab h).elim
  have h01_0 : τ (0, 1) {0} = 1 := hleft 0 1 (by decide)
  have h02_0 : τ (0, 2) {0} = 2 := hleft 0 2 (by decide)
  have h01_1 : τ (0, 1) {1} = 0 := hright 1 0 (by decide)
  have h12_1 : τ (1, 2) {1} = 2 := hleft 1 2 (by decide)
  have h02_2 : τ (0, 2) {2} = 0 := hright 2 0 (by decide)
  have h12_2 : τ (1, 2) {2} = 1 := hright 2 1 (by decide)
  have hfirst : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
    rcases hchoice 0 1 2 (by decide) with h12_0 | h12_0
    · have ha := hsum {0} (hI 0) 1
      have hb := hsum {0} (hI 0) 2
      rcases hchoice 1 0 2 (by decide) with h02_1 | h02_1
      · have hc := hsum {1} (hI 1) 2
        simp [h01_0, h02_0, h12_0, h01_1, h02_1, h12_1] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {1} (hI 1) 2
        simp [h01_0, h02_0, h12_0, h01_1, h02_1, h12_1] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
    · have ha := hsum {0} (hI 0) 1
      have hb := hsum {0} (hI 0) 2
      rcases hchoice 2 0 1 (by decide) with h01_2 | h01_2
      · have hc := hsum {2} (hI 2) 1
        simp [h01_0, h02_0, h12_0, h01_2, h02_2, h12_2] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {2} (hI 2) 1
        simp [h01_0, h02_0, h12_0, h01_2, h02_2, h12_2] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with h | h | h <;> subst e <;>
    simp only [hfirst.1, hfirst.2.1, hfirst.2.2]
