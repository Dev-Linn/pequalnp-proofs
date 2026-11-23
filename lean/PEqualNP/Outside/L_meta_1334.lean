import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1334

open PEqualNP.CircuitLowerBounds

-- Two gate lists that agree except at the gate producing wire p, where no gate of the first list
-- reads p, give wire lists that agree at every index other than p.
theorem foldl_agree (p : ℕ) : ∀ (gs gs' : List Gate) (a b : List Bool),
    gs.length = gs'.length →
    (∀ (k : ℕ) (g : Gate), gs[k]? = some g → p ∉ g.inputs) →
    (∀ k, a.length + k ≠ p → gs[k]? = gs'[k]?) →
    a.length = b.length → (∀ i, i ≠ p → a[i]? = b[i]?) →
    ∀ i, i ≠ p →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)[i]? =
        (gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b)[i]? := by
  intro gs
  induction gs with
  | nil =>
    intro gs' a b hlen _ _ _ h
    have : gs' = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst this
    exact h
  | cons g gs ih =>
    intro gs' a b hlen hno hsame hl h
    cases gs' with
    | nil => simp at hlen
    | cons g2 gs' =>
      simp only [List.foldl_cons]
      apply ih gs' _ _ (by simpa using hlen)
      · intro k g0 hk
        exact hno (k + 1) g0 (by simpa using hk)
      · intro k hk
        have := hsame (k + 1) (by simp at hk; omega)
        simpa using this
      · simp [hl]
      · intro i hi
        rw [List.getElem?_append, List.getElem?_append, ← hl]
        by_cases hlt : i < a.length
        · simp only [hlt, ite_true]
          exact h i hi
        · simp only [hlt, ite_false]
          by_cases heq : i = a.length
          · subst heq
            have hg : g = g2 := by
              have := hsame 0 (by omega)
              simpa using this
            subst hg
            have hgn : p ∉ g.inputs := hno 0 g (by simp)
            have hv : (g.inputs.map fun i => a.getD i false) =
                (g.inputs.map fun i => b.getD i false) := by
              apply List.map_congr_left
              intro u hu
              have hup : u ≠ p := fun e => hgn (e ▸ hu)
              simp only [List.getD_eq_getElem?_getD, h u hup]
            rw [hv]
          · have h1 : i - a.length ≠ 0 := by omega
            rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

end PEqualNP.Outside.L_meta_1334

theorem PEqualNP.Outside.L_meta_1334 : ∀ (n q w : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g' : PEqualNP.CircuitLowerBounds.Gate), (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gates[k]? = some g → n + q ∉ g.inputs) → w ≠ n + q → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set q g', w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) := by
  intro n q w gates g' hno hw x
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  congr 1
  symm
  apply PEqualNP.Outside.L_meta_1334.foldl_agree (n + q) gates (gates.set q g') _ _ (by simp) hno
  · intro k hk
    have hkq : q ≠ k := by simp at hk; omega
    rw [List.getElem?_set_ne hkq]
  · rfl
  · intro i _
    rfl
  · exact hw
