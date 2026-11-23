import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds

/-- Reading a coordinate other than the one that was overwritten does not change `getD`. -/
private lemma getD_set_false_of_ne {x : List Bool} {j k : ℕ} (h : k ≠ j) :
    (x.set j false).getD k false = x.getD k false := by
  by_cases hk : k < x.length
  · have hk' : k < (x.set j false).length := by simpa [List.length_set] using hk
    rw [List.getD_eq_getElem (l := x.set j false) (d := false) hk',
      List.getD_eq_getElem (l := x) (d := false) hk]
    exact List.getElem_set_ne (i := j) (j := k) (Ne.symm h) hk'
  · rw [List.getD_eq_default (l := x.set j false) (d := false)
        (by simpa [List.length_set] using Nat.le_of_not_lt hk),
      List.getD_eq_default (l := x) (d := false) (Nat.le_of_not_lt hk)]

/-- Every coordinate of the all-true input is `true`. -/
private lemma getD_replicate_true {n k : ℕ} (h : k < n) :
    (List.replicate n true).getD k false = true := by
  rw [List.getD_eq_getElem (l := List.replicate n true) (d := false) (by simpa using h)]
  simp

/-- Overwriting one coordinate with `false` makes the conjunction `false`. -/
private lemma all_set_false {x : List Bool} {j : ℕ} (hj : j < x.length) :
    (x.set j false).all id = false := by
  rw [List.all_eq_false]
  exact ⟨false, List.mem_set hj false, by simp⟩

/-- A circuit with at most one gate and fan-in at most one cannot decide the conjunction of
`n ≥ 2` bits: it depends on at most one input bit, while the conjunction depends on all. -/
theorem L_clb_034 :
    ∀ (n d : ℕ), 2 ≤ n →
      ({x : List Bool | x.all id = true} : Language Bool) ∉
        PEqualNP.CircuitLowerBounds.SizeDepth
          {PEqualNP.CircuitLowerBounds.GateOp.and,
           PEqualNP.CircuitLowerBounds.GateOp.or,
           PEqualNP.CircuitLowerBounds.GateOp.not}
          (fun m : ℕ => if m = n then 1 else m + 2) d := by
  intro n d hn hmem
  obtain ⟨C, hgates, hsize, _hdepth, hdec⟩ := hmem n
  have hsize1 : C.gates.length ≤ 1 := by simpa [Circuit.size] using hsize
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 1 := by
    intro g hg
    simpa using (hgates g hg).2
  let x : List Bool := List.replicate n true
  have hxlen : x.length = n := by simp [x]
  have hxall : x.all id = true := by simp [x]
  have hxeval : C.eval x = true := (hdec x hxlen).2 hxall
  -- Any `y` of length `n` with conjunction `false` contradicts the circuit.
  have contra : ∀ y : List Bool, y.length = n → y.all id = false →
      C.eval y = C.eval x → False := by
    intro y hylen hyall hyeq
    have hyev : C.eval y = true := by rw [hyeq]; exact hxeval
    have hyL : y.all id = true := (hdec y hylen).1 hyev
    rw [hyall] at hyL
    exact Bool.false_ne_true hyL
  rcases hgs : C.gates with _ | ⟨g, gs⟩
  · -- No gate: the output is an input wire or the default `false`.
    have hw : ∀ z : List Bool, C.wires z = z := by
      intro z
      simp [Circuit.wires, hgs]
    have hev : ∀ z : List Bool, C.eval z = z.getD C.output false := by
      intro z
      simp [Circuit.eval, hw z]
    by_cases hlt : C.output < n
    · let j : ℕ := if C.output = 0 then 1 else 0
      have hjlt : j < n := by dsimp [j]; split <;> omega
      have hjne : j ≠ C.output := by dsimp [j]; split <;> omega
      let y : List Bool := x.set j false
      have hylen : y.length = n := by simp [y, x]
      have hyall : y.all id = false := by
        apply all_set_false
        simpa [x] using hjlt
      have hyeq : C.eval y = C.eval x := by
        rw [hev y, hev x, getD_set_false_of_ne (j := j) (k := C.output) (Ne.symm hjne)]
      exact contra y hylen hyall hyeq
    · have hxfalse : C.eval x = false := by
        rw [hev x, List.getD_eq_default (l := x) (d := false)
          (by rw [hxlen]; exact Nat.le_of_not_lt hlt)]
      rw [hxfalse] at hxeval
      exact Bool.false_ne_true hxeval
  · -- One gate: the gate list is a singleton.
    have hgs_nil : gs = [] := by
      have h := hsize1
      rw [hgs] at h
      simp only [List.length_cons] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hw : ∀ z : List Bool,
        C.wires z = z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)] := by
      intro z
      simp [Circuit.wires, hgs, hgs_nil]
    have hev : ∀ z : List Bool,
        C.eval z = (z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]).getD
          C.output false := by
      intro z
      simp [Circuit.eval, hw z]
    by_cases hlt : C.output < n
    · let j : ℕ := if C.output = 0 then 1 else 0
      have hjlt : j < n := by dsimp [j]; split <;> omega
      have hjne : j ≠ C.output := by dsimp [j]; split <;> omega
      let y : List Bool := x.set j false
      have hylen : y.length = n := by simp [y, x]
      have hyall : y.all id = false := by
        apply all_set_false
        simpa [x] using hjlt
      have hyeq : C.eval y = C.eval x := by
        rw [hev y, hev x,
          List.getD_append _ _ _ _ (by simp [y, x]; omega),
          List.getD_append _ _ _ _ (by simp [x]; omega),
          getD_set_false_of_ne (j := j) (k := C.output) (Ne.symm hjne)]
      exact contra y hylen hyall hyeq
    · by_cases heq : C.output = n
      · -- The output is the single gate.
        have hev_gate : ∀ z : List Bool, z.length = n →
            C.eval z = g.op.eval (g.inputs.map fun i => z.getD i false) := by
          intro z hz
          rw [hev z, List.getD_append_right _ _ _ _
            (by rw [hz, heq])]
          rw [heq, hz]
          simp
        rcases hins : g.inputs with _ | ⟨i, ins⟩
        · -- The gate reads no wire: a constant.
          let j : ℕ := 0
          have hjlt : j < n := by dsimp [j]; omega
          let y : List Bool := x.set j false
          have hylen : y.length = n := by simp [y, x]
          have hyall : y.all id = false := by
            apply all_set_false
            simpa [x] using hjlt
          have hyeq : C.eval y = C.eval x := by
            rw [hev_gate y hylen, hev_gate x hxlen, hins]
            simp
          exact contra y hylen hyall hyeq
        · rcases ins with _ | ⟨i2, rest⟩
          · -- The gate reads exactly one wire `i`.
            by_cases hi : i < n
            · let j : ℕ := if i = 0 then 1 else 0
              have hjlt : j < n := by dsimp [j]; split <;> omega
              have hjne : j ≠ i := by dsimp [j]; split <;> omega
              let y : List Bool := x.set j false
              have hylen : y.length = n := by simp [y, x]
              have hyall : y.all id = false := by
                apply all_set_false
                simpa [x] using hjlt
              have hyeq : C.eval y = C.eval x := by
                rw [hev_gate y hylen, hev_gate x hxlen, hins]
                simp only [List.map_cons, List.map_nil]
                rw [getD_set_false_of_ne (j := j) (k := i) (Ne.symm hjne)]
              exact contra y hylen hyall hyeq
            · -- The gate reads a wire that does not exist: a constant on length `n`.
              let j : ℕ := 0
              have hjlt : j < n := by dsimp [j]; omega
              let y : List Bool := x.set j false
              have hylen : y.length = n := by simp [y, x]
              have hyall : y.all id = false := by
                apply all_set_false
                simpa [x] using hjlt
              have hyeq : C.eval y = C.eval x := by
                rw [hev_gate y hylen, hev_gate x hxlen, hins]
                simp only [List.map_cons, List.map_nil]
                have hyi : y.getD i false = false := by
                  refine List.getD_eq_default (l := y) (d := false) ?_
                  change (x.set j false).length ≤ i
                  rw [List.length_set, hxlen]
                  exact Nat.le_of_not_lt hi
                have hxi : x.getD i false = false := by
                  refine List.getD_eq_default (l := x) (d := false) ?_
                  rw [hxlen]
                  exact Nat.le_of_not_lt hi
                rw [hyi, hxi]
              exact contra y hylen hyall hyeq
          · -- Two or more wires contradict the fan-in bound.
            exfalso
            have hlen := hfan g (by simp [hgs])
            rw [hins] at hlen
            simp only [List.length_cons] at hlen
            omega
      · -- The output wire does not exist on length `n`.
        have hxfalse : C.eval x = false := by
          rw [hev x]
          refine List.getD_eq_default
            (l := x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) (d := false) ?_
          simp only [List.length_append, List.length_singleton, hxlen]
          omega
        rw [hxfalse] at hxeval
        exact Bool.false_ne_true hxeval

end PEqualNP.Outside
