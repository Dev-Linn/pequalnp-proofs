import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_461 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6, (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 6 × Fin 6 → ℚ, (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hsum e he
  subst E
  have hI (i : Fin 6) :
      ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)),
        ¬ (f.1 ∈ ({i} : Finset (Fin 6)) ∧ f.2 ∈ ({i} : Finset (Fin 6))) := by
    fin_cases i <;> decide
  have hchoice (i a b : Fin 6) (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6))) :
      τ (a, b) {i} = a ∨ τ (a, b) {i} = b :=
    (hτ (a, b) hab {i} (hI i)).1
  have hnot (i a b : Fin 6) (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6))) : τ (a, b) {i} ≠ i := by
    simpa using (hτ (a, b) hab {i} (hI i)).2
  have hleft (i b : Fin 6) (hab : (i, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6))) : τ (i, b) {i} = b := by
    rcases hchoice i i b hab with h | h
    · exact (hnot i i b hab h).elim
    · exact h
  have hright (i a : Fin 6) (hab : (a, i) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6))) : τ (a, i) {i} = a := by
    rcases hchoice i a i hab with h | h
    · exact h
    · exact (hnot i a i hab h).elim
  have haway (i a b v : Fin 6) (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6))) (hav : a ≠ v) (hbv : b ≠ v) :
      τ (a, b) {i} ≠ v := by
    rcases hchoice i a b hab with h | h
    · simpa [h] using hav
    · simpa [h] using hbv
  have hp03 : c (0, 3) = 0 := by
    have h := hsum {0} (hI 0) 3
    simp [hleft, hright, haway] at h
    exact h
  have hp14 : c (1, 4) = 0 := by
    have h := hsum {1} (hI 1) 4
    simp [hleft, hright, haway] at h
    exact h
  have hp25 : c (2, 5) = 0 := by
    have h := hsum {2} (hI 2) 5
    simp [hleft, hright, haway] at h
    exact h
  have hzero : ∀ (p : Fin 6 × Fin 6 → Bool) (l : List (Fin 6 × Fin 6)), (∀ a ∈ l, c a = 0) →
      (List.map c (List.filter p l)).sum = 0 := by
    intro p l hl
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hl a (List.mem_of_mem_filter ha)
  have hfirst : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
    rcases hchoice 0 1 2 (by decide) with h12_0 | h12_0
    · have ha := hsum {0} (hI 0) 1
      have hb := hsum {0} (hI 0) 2
      rcases hchoice 1 0 2 (by decide) with h02_1 | h02_1
      · have hc := hsum {1} (hI 1) 2
        simp [hleft, hright, haway, h12_0, h02_1, hp03, hp14, hp25, hzero] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {1} (hI 1) 2
        simp [hleft, hright, haway, h12_0, h02_1, hp03, hp14, hp25, hzero] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
    · have ha := hsum {0} (hI 0) 1
      have hb := hsum {0} (hI 0) 2
      rcases hchoice 2 0 1 (by decide) with h01_2 | h01_2
      · have hc := hsum {2} (hI 2) 1
        simp [hleft, hright, haway, h12_0, h01_2, hp03, hp14, hp25, hzero] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {2} (hI 2) 1
        simp [hleft, hright, haway, h12_0, h01_2, hp03, hp14, hp25, hzero] at ha hb hc
        exact ⟨by linarith, by linarith, by linarith⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with h | h | h | h | h | h <;> subst e <;>
    simp only [hfirst.1, hfirst.2.1, hfirst.2.2, hp03, hp14, hp25]
