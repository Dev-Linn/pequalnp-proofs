import PEqualNP.Defs

-- Adapted from the project proof L_meta_2335.
namespace PEqualNP.Outside.L_meta_2895
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj


def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def readTag (t : Bool ⊕ (Bool × ℕ)) (w : List Bool) : Bool :=
  match t with
  | .inl c => c
  | .inr (invert, i) => if invert then !(w.getD i false) else w.getD i false

lemma secondForm (g : Gate) (hg : Ok g) (h9 : 9 ∈ g.inputs) :
    ∃ t, ∀ w : List Bool, w.getD 9 false = false → gateValue g w = readTag t w := by
  rcases g with ⟨op, ins⟩
  have hlen : ins.length ≤ 2 := hg.2
  have hop : op = .and ∨ op = .or ∨ op = .not := hg.1
  change 9 ∈ ins at h9
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · simp at h9
  · have e : 9 = a := by simpa using h9
    subst a
    rcases hop with rfl | rfl | rfl
    · exact ⟨.inl false, fun w hw => by simp [gateValue, readTag, GateOp.eval, show w[9]?.getD false = false from hw]⟩
    · exact ⟨.inl false, fun w hw => by simp [gateValue, readTag, GateOp.eval, show w[9]?.getD false = false from hw]⟩
    · exact ⟨.inl true, fun w hw => by simp [gateValue, readTag, GateOp.eval, show w[9]?.getD false = false from hw]⟩
  · rcases hop with rfl | rfl | rfl
    · refine ⟨.inl false, fun w hw => ?_⟩
      rcases (show 9 = a ∨ 9 = b by simpa using h9) with rfl | rfl <;>
        simp [gateValue, readTag, GateOp.eval, show w[9]?.getD false = false from hw]
    · rcases (show 9 = a ∨ 9 = b by simpa using h9) with rfl | rfl
      · exact ⟨.inr (false, b), fun w hw => by simp [gateValue, readTag, GateOp.eval, show w[9]?.getD false = false from hw]⟩
      · exact ⟨.inr (false, a), fun w hw => by simp [gateValue, readTag, GateOp.eval, show w[9]?.getD false = false from hw]⟩
    · exact ⟨.inr (true, a), fun w _ => by simp [gateValue, readTag, GateOp.eval]⟩
  · simp at hlen

lemma agreeOutside (B : ℕ → Prop) (gs : List Gate) (w w' : List Bool)
    (hno : ∀ g ∈ gs, ∀ j ∈ g.inputs, ¬ B j)
    (hlen : w.length = w'.length)
    (heq : ∀ j, ¬ B j → w.getD j false = w'.getD j false) :
    ∀ j, ¬ B j → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs generalizing w w' with
  | nil => exact heq
  | cons g gs ih =>
    have e : gateValue g w = gateValue g w' := by
      unfold gateValue
      congr 1
      apply List.map_congr_left
      intro j hj
      exact heq j (hno g List.mem_cons_self j hj)
    apply ih (w ++ [gateValue g w]) (w' ++ [gateValue g w'])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hlen])
    intro j hj
    by_cases h : j = w.length
    · rw [h, getD_snoc_eq, hlen, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ h, getD_snoc_ne _ _ _ _ (by omega)]
      exact heq j hj


def restriction (x : Fin 8 → Bool) : Fin 9 → Bool :=
  Fin.insertNth (6 : Fin 9) false x

def headWires (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 && x 6]

def inputs (i : Fin 8) (σ : Fin 8 → Fin 8) (y : Fin 8 → Bool) : List Bool :=
  List.ofFn y ++ [!y (σ i)]

lemma prefix_length (x : Fin 9 → Bool) : (headWires x).length = 10 := by simp [headWires]

lemma prefix_nine (x : Fin 9 → Bool) : (headWires x).getD 9 false = (x 0 && x 6) := by
  unfold headWires
  exact getD_snoc_len _ _ _ _ (by simp)

lemma ofFn_wire {n : ℕ} {α : Type} (f : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn f).getD i d = f i := by simp

lemma prefix_input (x : Fin 9 → Bool) (j : Fin 9) :
    (headWires x).getD j false = x j := by
  rw [headWires, List.getD_append _ _ _ _ (by simpa using j.isLt)]
  exact ofFn_wire x false j

lemma prefix_restrict_six (x : Fin 8 → Bool) : (headWires (restriction x)).getD 6 false = false := by
  simpa [restriction] using prefix_input (restriction x) (6 : Fin 9)

lemma prefix_restrict_nine (x : Fin 8 → Bool) : (headWires (restriction x)).getD 9 false = false := by
  rw [prefix_nine]
  simp [restriction]

lemma prefix_restrict_above (x : Fin 8 → Bool) (j : ℕ) (hj : 9 ≤ j) :
    (headWires (restriction x)).getD j false = false := by
  by_cases h : j = 9
  · exact h ▸ prefix_restrict_nine x
  · exact List.getD_eq_default _ _ (by rw [prefix_length]; omega)

lemma input_wire (i : Fin 8) (σ : Fin 8 → Fin 8) (y : Fin 8 → Bool) (j : Fin 8) :
    (inputs i σ y).getD j false = y j := by
  rw [inputs, List.getD_append _ _ _ _ (by simpa using j.isLt)]
  exact ofFn_wire y false j

lemma input_negated (i : Fin 8) (σ : Fin 8 → Fin 8) (y : Fin 8 → Bool) :
    (inputs i σ y).getD 8 false = !y (σ i) := by
  unfold inputs
  exact getD_snoc_len _ _ _ _ (by simp)

lemma representSecond (t : Bool ⊕ (Bool × ℕ)) :
    ∃ i : Fin 8, ∀ σ : Fin 8 → Fin 8, ∃ s : Stat,
      s.Valid 9 ∧
      (∀ inv, t = .inr (inv, 6) → ∃ b, s = .inl b) ∧
      ∀ y, s.val (inputs i σ y) = readTag t (headWires (restriction (y ∘ σ))) := by
  rcases t with b | ⟨inv, j⟩
  · exact ⟨0, fun _ => ⟨.inl b, trivial, fun _ _ => ⟨b, rfl⟩, fun _ => rfl⟩⟩
  by_cases h6 : j = 6
  · subst j
    refine ⟨0, fun _ => ⟨.inl inv, trivial, fun _ _ => ⟨inv, rfl⟩, fun y => ?_⟩⟩
    rw [readTag, prefix_restrict_six]; cases inv <;> rfl
  by_cases hj : j < 9
  · have hfin : (⟨j, hj⟩ : Fin 9) ≠ 6 := by
      intro e
      exact h6 (congrArg Fin.val e)
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hfin
    have hread (x : Fin 8 → Bool) :
        (headWires (restriction x)).getD j false = x i := by
      change (headWires (restriction x)).getD (⟨j, hj⟩ : Fin 9).val false = x i
      rw [prefix_input, ← hi]
      simp [restriction]
    cases inv
    · refine ⟨i, fun σ => ⟨.inr (σ i).val, by simp [Stat.Valid]; omega, ?_, fun y => ?_⟩⟩
      · simp [h6]
      · simp only [Stat.val, input_wire, readTag, hread, Bool.false_eq_true, ite_false, Function.comp_apply]
    · refine ⟨i, fun σ => ⟨.inr 8, by change 8 < 9; decide, ?_, fun y => ?_⟩⟩
      · simp [h6]
      · simp only [Stat.val, input_negated, readTag, hread, ite_true, Function.comp_apply]
  · exact ⟨0, fun _ => ⟨.inl inv, trivial, fun _ _ => ⟨inv, rfl⟩, fun y => by
      rw [readTag, prefix_restrict_above _ j (by omega)]; cases inv <;> rfl⟩⟩


def seed (σ : Fin 8 → Fin 8) (s : Stat) : List Stat :=
  List.ofFn (Fin.insertNth (6 : Fin 9) (.inl false) (fun j => .inr (σ j).val)) ++
    [.inl false, s]

lemma seed_six (σ : Fin 8 → Fin 8) (s : Stat) :
    (seed σ s).getD 6 (.inl false) = .inl false := by
  unfold seed
  rw [List.getD_append _ _ _ _ (by simp)]
  change (List.ofFn _).getD (6 : Fin 9).val _ = _
  rw [ofFn_wire]
  exact Fin.insertNth_apply_same _ _ _

lemma seed_ten (σ : Fin 8 → Fin 8) (s : Stat) : (seed σ s).getD 10 (.inl false) = s := by
  unfold seed
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma seedInv (i : Fin 8) (σ : Fin 8 → Fin 8) (y : Fin 8 → Bool) (s : Stat)
    (hs : s.Valid 9) (b : Bool) (hb : s.val (inputs i σ y) = b) :
    Inv 9 (inputs i σ y) (headWires (restriction (y ∘ σ)) ++ [b]) (seed σ s, []) := by
  refine ⟨by simp [seed, prefix_length], ?_⟩
  intro j
  change ((seed σ s).getD j (.inl false)).Valid 9 ∧
    ((seed σ s).getD j (.inl false)).val (inputs i σ y) =
      (headWires (restriction (y ∘ σ)) ++ [b]).getD j false
  by_cases hj : j < 9
  · have seed_read : (seed σ s).getD j (.inl false) =
        Fin.insertNth (α := fun _ => Stat) (6 : Fin 9) (Sum.inl false) (fun k => Sum.inr (σ k).val) ⟨j, hj⟩ := by
      unfold seed
      rw [List.getD_append _ _ _ _ (by simpa)]
      change (List.ofFn _).getD (⟨j, hj⟩ : Fin 9).val _ = _
      exact ofFn_wire _ _ _
    rw [seed_read, List.getD_append _ _ _ _ (by rw [prefix_length]; omega)]
    change _ ∧ _ = (headWires (restriction (y ∘ σ))).getD (⟨j, hj⟩ : Fin 9).val false
    rw [prefix_input]
    generalize (⟨j, hj⟩ : Fin 9) = k
    induction k using (6 : Fin 9).succAboveCases with
    | x => simp [restriction, Stat.Valid, Stat.val]
    | p k =>
      rw [Fin.insertNth_apply_succAbove]
      refine ⟨Nat.lt_trans (σ k).isLt (by decide), ?_⟩
      change (inputs i σ y).getD (σ k).val false = _
      rw [input_wire]
      exact (Fin.insertNth_apply_succAbove (α := fun _ => Bool) (6 : Fin 9) false (y ∘ σ) k).symm
  · by_cases h9 : j = 9
    · subst j
      have zz : (seed σ s).getD 9 (.inl false) = .inl false := by
        unfold seed
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
      rw [zz, List.getD_append _ _ _ _ (by rw [prefix_length]; decide)]
      rw [prefix_restrict_nine]; exact ⟨trivial, rfl⟩
    · by_cases h10 : j = 10
      · subst j
        rw [seed_ten, getD_snoc_len _ _ _ _ (prefix_length _)]
        exact ⟨hs, hb⟩
      · rw [List.getD_eq_default _ _ (by simp [seed]; omega),
            List.getD_eq_default _ _ (by simp [prefix_length]; omega)]
        exact ⟨trivial, rfl⟩

lemma finishCircuit (gs : List Gate) (hgs : ∀ g ∈ gs, NOk g) (o : ℕ)
    (f : (Fin 9 → Bool) → Bool) (t : Bool ⊕ (Bool × ℕ))
    (heval : ∀ x : Fin 8 → Bool,
      (wiresFrom gs (headWires (restriction x) ++ [readTag t (headWires (restriction x))])).getD o false =
        f (restriction x))
    (hnc : f (restriction (fun _ => false)) ≠ f (restriction (fun _ => true)))
    (hreader : (∃ g ∈ gs, 6 ∈ g.inputs) ∨
      ((∃ inv, t = .inr (inv, 6)) ∧ ∃ g ∈ gs, 10 ∈ g.inputs)) :
    ∃ i : Fin 8, ∀ σ : Fin 8 → Fin 8, ∃ D : Circuit,
      FanInTwo D ∧ D.size + 1 ≤ gs.length ∧
      ∀ y, D.eval (inputs i σ y) = f (restriction (y ∘ σ)) := by
  obtain ⟨i, hi⟩ := representSecond t
  refine ⟨i, fun σ => ?_⟩
  obtain ⟨s, hs, hconst, hsval⟩ := hi σ
  let acc : List Stat × List Gate := (seed σ s, [])
  let simpTail := elim 9 gs acc
  have hlen : simpTail.2.length + 1 ≤ gs.length := by
    rcases hreader with h6 | ⟨⟨inv, ht⟩, h10⟩
    · simpa [simpTail, acc] using
        elim_len_lt 9 6 gs acc hgs (by simp [acc, seed]) ⟨false, seed_six σ s⟩ h6
    · obtain ⟨b, hb⟩ := hconst inv ht
      simpa [simpTail, acc] using
        elim_len_lt 9 10 gs acc hgs (by simp [acc, seed]) ⟨b, (seed_ten σ s).trans hb⟩ h10
  have sound (y : Fin 8 → Bool) :
      (simpTail.1.getD o (.inl false)).val (wiresFrom simpTail.2 (inputs i σ y)) =
        f (restriction (y ∘ σ)) := by
    have H := inv_elim 9 (inputs i σ y) (by simp [inputs]) gs _ acc
      (fun g hg => (hgs g hg).1) (seedInv i σ y s hs _ (hsval y))
    exact (H.2 o).2.trans (heval _)
  cases hout : simpTail.1.getD o (.inl false) with
  | inl b =>
    exfalso
    apply hnc
    have hfalse := sound (fun _ => false)
    have htrue := sound (fun _ => true)
    rw [hout] at hfalse htrue
    exact hfalse.symm.trans htrue
  | inr j =>
    refine ⟨⟨simpTail.2, j⟩, elim_ok 9 gs acc (by simp [acc]), hlen, ?_⟩
    intro y
    change (wiresFrom simpTail.2 (inputs i σ y)).getD j false = _
    simpa only [hout, Stat.val] using sound y


def sampleA (j : Fin 9) : Bool := decide (j = 1)
def sampleB (j : Fin 9) : Bool := decide (j = 1 ∨ j = 6)

lemma samplesAgree (j : ℕ) (hj : j ≠ 6) :
    (headWires sampleA).getD j false = (headWires sampleB).getD j false := by
  by_cases h : j < 10
  · interval_cases j <;> first | contradiction | decide +kernel
  · rw [List.getD_eq_default _ _ (by simpa [prefix_length] using h),
        List.getD_eq_default _ _ (by simpa [prefix_length] using h)]

lemma tagSamples (t : Bool ⊕ (Bool × ℕ))
    (ht : ¬ ∃ inv, t = .inr (inv, 6)) :
    readTag t (headWires sampleA) = readTag t (headWires sampleB) := by
  rcases t with c | ⟨inv, j⟩
  · rfl
  have h6 : j ≠ 6 := by
    intro e
    subst j
    exact ht ⟨inv, rfl⟩
  simp only [readTag, samplesAgree j h6]

lemma findReader (gs : List Gate) (o : ℕ) (f : (Fin 9 → Bool) → Bool)
    (t : Bool ⊕ (Bool × ℕ))
    (heval : ∀ x : Fin 9 → Bool, (headWires x).getD 9 false = false →
      (wiresFrom gs (headWires x ++ [readTag t (headWires x)])).getD o false = f x)
    (hdep : f sampleA ≠ f sampleB)
    (hnc : f (restriction (fun _ => false)) ≠ f (restriction (fun _ => true))) :
    (∃ g ∈ gs, 6 ∈ g.inputs) ∨
      ((∃ inv, t = .inr (inv, 6)) ∧ ∃ g ∈ gs, 10 ∈ g.inputs) := by
  by_cases h6 : ∃ g ∈ gs, 6 ∈ g.inputs
  · exact Or.inl h6
  push Not at h6
  have out6 : o ≠ 6 := by
    intro e
    subst o
    apply hnc
    have z (y : Fin 8 → Bool) : f (restriction y) = false := by
      rw [← heval _ (prefix_restrict_nine y)]
      rw [getD_wiresFrom _ _ _ (by simp [prefix_length])]
      rw [List.getD_append _ _ _ _ (by rw [prefix_length]; decide)]
      exact prefix_restrict_six y
    rw [z, z]
  have sa := heval sampleA (by decide +kernel)
  have sb := heval sampleB (by decide +kernel)
  by_cases ht : ∃ inv, t = .inr (inv, 6)
  · right
    refine ⟨ht, ?_⟩
    by_contra! h10
    obtain ⟨inv, rfl⟩ := ht
    have out10 : o ≠ 10 := by
      intro e
      subst o
      apply hnc
      have z (y : Fin 8 → Bool) : f (restriction y) = inv := by
        rw [← heval _ (prefix_restrict_nine y)]
        rw [getD_wiresFrom _ _ _ (by simp [prefix_length])]
        rw [getD_snoc_len _ _ _ _ (prefix_length _)]
        rw [readTag, prefix_restrict_six]; cases inv <;> rfl
      rw [z, z]
    apply hdep
    rw [← sa, ← sb]
    apply agreeOutside (fun j => j = 6 ∨ j = 10) gs _ _
    · intro g hg j hj
      rintro (rfl | rfl)
      · exact h6 g hg hj
      · exact h10 g hg hj
    · simp [prefix_length]
    · intro j hj
      have e6 : j ≠ 6 := fun e => hj (Or.inl e)
      have e10 : j ≠ 10 := fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by simpa [prefix_length] using e10),
          getD_snoc_ne _ _ _ _ (by simpa [prefix_length] using e10)]
      exact samplesAgree j e6
    · exact fun h => h.elim out6 out10
  · exfalso
    apply hdep
    rw [← sa, ← sb]
    apply agree_except 6 gs _ _ h6 (by simp [prefix_length]) _ _ out6
    intro j hj
    by_cases e10 : j = 10
    · subst j
      rw [getD_snoc_len _ _ _ _ (prefix_length _), getD_snoc_len _ _ _ _ (prefix_length _)]
      exact tagSamples t ht
    · rw [getD_snoc_ne _ _ _ _ (by simpa [prefix_length] using e10),
          getD_snoc_ne _ _ _ _ (by simpa [prefix_length] using e10)]
      exact samplesAgree j hj


lemma project (f : (Fin 9 → Bool) → Bool) (hdep : f sampleA ≠ f sampleB)
    (hnc : f (restriction (fun _ => false)) ≠ f (restriction (fun _ => true)))
    (C : Circuit) (hsecond : ∃ g ∈ C.gates[1]?.toList, 9 ∈ g.inputs)
    (hfan : FanInTwo C) (hfirst : ∀ x : Fin 9 → Bool,
      (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 6))
    (hf : circuitFun 9 C = f) :
    ∃ i : Fin 8, ∀ σ : Fin 8 → Fin 8, ∃ D : Circuit, FanInTwo D ∧
      D.size + 3 ≤ C.size ∧
      ∀ y : Fin 8 → Bool, D.eval (inputs i σ y) = f (restriction (y ∘ σ)) := by
  rcases C with ⟨gates, o⟩
  rcases gates with _ | ⟨g, _ | ⟨g', tail⟩⟩
  · simp at hsecond
  · simp at hsecond
  have h9 : 9 ∈ g'.inputs := by simpa using hsecond
  have htail : ∀ h ∈ tail, Ok h := fun h hh =>
    hfan h (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hh))
  have hon : ∀ h ∈ tail.map normGate, NOk h := by
    intro h hh
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hh
    exact normGate_nok a (htail a ha)
  obtain ⟨t, ht⟩ := secondForm g' (hfan g' (by simp)) h9
  have hhead (x : Fin 9 → Bool) :
      List.ofFn x ++ [gateValue g (List.ofFn x)] = headWires x := by
    have first := hfirst x
    change (wiresFrom (g' :: tail) (List.ofFn x ++ [gateValue g (List.ofFn x)])).getD 9 false = _ at first
    rw [getD_wiresFrom _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)] at first
    rw [headWires, first]
  have heval (x : Fin 9 → Bool) (hx : (headWires x).getD 9 false = false) :
      (wiresFrom (tail.map normGate) (headWires x ++ [readTag t (headWires x)])).getD o false =
        f x := by
    rw [wiresFrom_norm, ← ht _ hx, ← hhead]
    exact congrFun hf x
  obtain ⟨i, H⟩ := finishCircuit (tail.map normGate) hon o f t
    (fun x => heval _ (prefix_restrict_nine x)) hnc (findReader _ _ _ _ heval hdep hnc)
  refine ⟨i, fun σ => ?_⟩
  obtain ⟨D, hD, hsize, hy⟩ := H σ
  refine ⟨D, hD, ?_, hy⟩
  simp only [List.length_map, Circuit.size] at hsize
  simp only [Circuit.size, List.length_cons]
  omega

end PEqualNP.Outside.L_meta_2895

theorem PEqualNP.Outside.L_meta_2895 : ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool), ((x1 fun (x2 : Fin (9 : ℕ)) => Decidable.decide (x2 = (1 : Fin (9 : ℕ)))) ≠ x1 fun (x2 : Fin (9 : ℕ)) => Decidable.decide (x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)))) → x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false fun (x3 : Fin (8 : ℕ)) => Bool.false) ≠ x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false fun (x3 : Fin (8 : ℕ)) => Bool.true) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∃ x5 ∈ x4.gates[(1 : ℕ)]?.toList, (9 : ℕ) ∈ x5.inputs) → PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x4.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = (x7 (0 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x4 = x1 → ∃ (x9 : Fin (8 : ℕ)), ∀ (x10 : Fin (8 : ℕ) → Fin (8 : ℕ)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (3 : ℕ) ≤ x4.size ∧ ∀ (x12 : Fin (8 : ℕ) → Bool), x11.eval (List.ofFn x12 ++ [!x12 (x10 x9)]) = x1 (Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false (x12 ∘ x10)) := by
  exact PEqualNP.Outside.L_meta_2895.project
