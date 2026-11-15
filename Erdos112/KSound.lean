import Erdos112.SearchSound
import Erdos112.KCover
import Erdos112.KCheck.All

/-!
# Soundness of the kernel search of Lemma 8

`no_graph32` and `no_graph23`: no `{I_4, L_3}`-free oriented graph on `Fin 14` agrees with the
fixed pairs of type (3,2) or (2,3). Both follow from the kernel computations `covered_Js`
(`KCover.lean`) and `all32`, `all23` (`KCheck/`), with no `native_decide`.

The argument, for a graph `D` that agrees with the fixed pairs:

1. `rowsJ D`, the table of `D` on `J = {6, ..., 13}`, is reached by step 1 of the search
   (`jsearch_true`), so it is one of the 24 tables of `KData.lean` (`covered_Js`).
2. For each vertex `v`, the row `att D v` of `v` over `J` is in the list of attachments
   (`att_mem`). The rows of the five neighbours of `0` pass every test of step 2
   (`stage2_true`): each test that fails would give a transitive triangle or four pairwise
   non-adjacent vertices in `D`.
3. Step 2 returns `false` on each of the 24 tables (`all32`, `all23`). Contradiction.
-/

namespace Erdos112.K

open Erdos112 Erdos112.Search
open scoped Classical

/-! ### Bit masks -/

theorem z_true {a : Nat} (h : a = 0) : z a = true := by subst h; rfl

theorem tb_eq (m j : Nat) : tb m j = m.testBit j := by
  have h : Nat.land (Nat.shiftRight m j) 1 = (m >>> j) % 2 := Nat.and_one_is_mod _
  unfold tb
  rw [h]
  simp only [Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (m >>> j) with h2 | h2 <;> rw [h2] <;> rfl

theorem land_tb {a b i : Nat} (h : (Nat.land a b).testBit i = true) :
    a.testBit i = true ∧ b.testBit i = true := by
  have h' : (a &&& b).testBit i = true := h
  rw [Nat.testBit_and, Bool.and_eq_true] at h'
  exact h'

theorem land_bit {a b : Nat} (h : Nat.land a b ≠ 0) :
    ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
  exact ⟨i, land_tb hi⟩

theorem z_land {a b : Nat} (h : ∀ i, a.testBit i = true → b.testBit i = true → False) :
    z (Nat.land a b) = true := by
  apply z_true
  by_contra hne
  obtain ⟨i, h1, h2⟩ := land_bit hne
  exact h i h1 h2

theorem lor_tb (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i

/-- The number whose bit `j` (for `j < n`) is `f j`. -/
def mk (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => mk f n + (if f n then 2 ^ n else 0)

theorem mk_lt (f : Nat → Bool) : ∀ n, mk f n < 2 ^ n := by
  intro n
  induction n with
  | zero => simp [mk]
  | succ n ih =>
    unfold mk
    rw [Nat.pow_succ]
    split <;> omega

theorem mk_bit (f : Nat → Bool) (n i : Nat) :
    (mk f n).testBit i = true ↔ i < n ∧ f i = true := by
  induction n with
  | zero => simp [mk]
  | succ n ih =>
    unfold mk
    by_cases hf : f n = true
    · rw [ite_eq_left hf, Nat.add_comm]
      rcases Nat.lt_trichotomy i n with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]
        exact ⟨fun ⟨_, h2⟩ => ⟨by omega, h2⟩, fun ⟨_, h2⟩ => ⟨h, h2⟩⟩
      · subst h
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (mk_lt f i)]
        simp [hf]
      · have hlt : 2 ^ n + mk f n < 2 ^ i := by
          have h1 := mk_lt f n
          have h2 : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) h
          rw [Nat.pow_succ] at h2
          omega
        rw [Nat.testBit_lt_two_pow hlt]
        constructor
        · intro h'; cases h'
        · rintro ⟨h', _⟩; omega
    · rw [ite_eq_right hf, Nat.add_zero, ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_or_ge i n with h | h
        · exact h
        · have : i = n := by omega
          subst this
          exact absurd h2 hf

/-! ### The rows of a graph -/

/-- The vertex `J j`, that is, `j + 6`. -/
def Jv (j : Nat) : Fin 14 := ⟨(j + 6) % 14, Nat.mod_lt _ (by decide)⟩

theorem Jv_val {j : Nat} (h : j < 8) : (Jv j).val = j + 6 := Nat.mod_eq_of_lt (by omega)

theorem Jv_ne {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) : Jv i ≠ Jv j := by
  intro e
  have := congrArg Fin.val e
  rw [Jv_val hi, Jv_val hj] at this
  omega

theorem lt6_ne {v : Fin 14} (hv : v.val < 6) {j : Nat} (hj : j < 8) : v ≠ Jv j := by
  intro e
  have := congrArg Fin.val e
  rw [Jv_val hj] at this
  omega

/-- `x` and `y` are not adjacent. -/
def NA (D : OGraph (Fin 14)) (x y : Fin 14) : Prop := ¬ D.arc x y ∧ ¬ D.arc y x

theorem NA.symm {D : OGraph (Fin 14)} {x y : Fin 14} (h : NA D x y) : NA D y x := ⟨h.2, h.1⟩

/-- The row of `v` over `J 0, ..., J (n-1)` in the graph `D`. -/
noncomputable def tr (D : OGraph (Fin 14)) (v : Fin 14) (n : Nat) : Row :=
  ⟨mk (fun j => decide (D.arc v (Jv j))) n, mk (fun j => decide (D.arc (Jv j) v)) n,
    mk (fun j => decide (NA D v (Jv j))) n⟩

theorem tr_o {D : OGraph (Fin 14)} {v : Fin 14} {n i : Nat} :
    (tr D v n).o.testBit i = true ↔ i < n ∧ D.arc v (Jv i) := by simp [tr, mk_bit]

theorem tr_i {D : OGraph (Fin 14)} {v : Fin 14} {n i : Nat} :
    (tr D v n).i.testBit i = true ↔ i < n ∧ D.arc (Jv i) v := by simp [tr, mk_bit]

theorem tr_n {D : OGraph (Fin 14)} {v : Fin 14} {n i : Nat} :
    (tr D v n).n.testBit i = true ↔ i < n ∧ NA D v (Jv i) := by simp [tr, mk_bit]

theorem tr_succ_o {D : OGraph (Fin 14)} {v : Fin 14} {j : Nat} (h : D.arc v (Jv j)) :
    tr D v (j + 1) = ⟨(tr D v j).o + 2 ^ j, (tr D v j).i, (tr D v j).n⟩ := by
  have h2 : ¬ D.arc (Jv j) v := D.asymm _ _ h
  have h3 : ¬ NA D v (Jv j) := fun h' => h'.1 h
  simp [tr, mk, h, h2, h3]

theorem tr_succ_i {D : OGraph (Fin 14)} {v : Fin 14} {j : Nat} (h : D.arc (Jv j) v) :
    tr D v (j + 1) = ⟨(tr D v j).o, (tr D v j).i + 2 ^ j, (tr D v j).n⟩ := by
  have h2 : ¬ D.arc v (Jv j) := D.asymm _ _ h
  have h3 : ¬ NA D v (Jv j) := fun h' => h'.2 h
  simp [tr, mk, h, h2, h3]

theorem tr_succ_n {D : OGraph (Fin 14)} {v : Fin 14} {j : Nat} (h : NA D v (Jv j)) :
    tr D v (j + 1) = ⟨(tr D v j).o, (tr D v j).i, (tr D v j).n + 2 ^ j⟩ := by
  simp [tr, mk, h, h.1, h.2]

/-- The row of `J j` over `J 0, ..., J (j-1)`. -/
noncomputable def rowJ (D : OGraph (Fin 14)) (j : Nat) : Row := tr D (Jv j) j

/-- The table of `D` on `J`. -/
noncomputable def rowsJ (D : OGraph (Fin 14)) : List Row := (List.range 8).map (rowJ D)

/-- The row of `v` over all of `J`. -/
noncomputable def att (D : OGraph (Fin 14)) (v : Fin 14) : Row := tr D v 8

/-- Four distinct pairwise non-adjacent vertices contradict `I_4`-freeness. -/
theorem indep4 (D : OGraph (Fin 14)) (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4)
    (a b c d : Fin 14) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (nab : NA D a b) (nac : NA D a c) (nad : NA D a d) (nbc : NA D b c)
    (nbd : NA D b d) (ncd : NA D c d) : False := by
  refine hI {a, b, c, d} ?_ ?_
  · intro p hp q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first
        | exact D.arc_irrefl _ | exact nab.1 | exact nab.2 | exact nac.1 | exact nac.2
        | exact nad.1 | exact nad.2 | exact nbc.1 | exact nbc.2 | exact nbd.1 | exact nbd.2
        | exact ncd.1 | exact ncd.2
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

/-! ### The list of rows contains the row of the graph -/

theorem gen_mem (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT) (chk3 : Bool)
    (allow : Nat → Nat → Bool) (v : Fin 14) (n : Nat)
    (h0 : ∀ j, j < n → NA D v (Jv j) → allow j 0 = true)
    (h1 : ∀ j, j < n → D.arc v (Jv j) → allow j 1 = true)
    (h2 : ∀ j, j < n → D.arc (Jv j) v → allow j 2 = true)
    (h3 : chk3 = true → ∀ i j, i < j → j < n →
      NA D (Jv j) (Jv i) → NA D v (Jv i) → NA D v (Jv j) → False) :
    ∀ m j, j + m = n →
      tr D v n ∈ gen chk3 allow ((List.range' j m).map (rowJ D)) j (tr D v j) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    have : j = n := by omega
    subst this
    simp [gen]
  | succ m ih =>
    intro j hj
    have hjn : j < n := by omega
    have ih' := ih (j + 1) (by omega)
    rw [List.range'_succ, List.map_cons, gen]
    by_cases a1 : D.arc v (Jv j)
    · rw [tr_succ_o a1] at ih'
      apply List.mem_append_right
      apply List.mem_append_left
      rw [ite_eq_left]
      · exact ih'
      · rw [Bool.and_eq_true, Bool.and_eq_true]
        refine ⟨⟨h1 j hjn a1, z_land ?_⟩, z_land ?_⟩
        · intro i hi1 hi2
          rw [lor_tb, Bool.or_eq_true] at hi1
          rw [tr_o] at hi2
          rcases hi1 with hi1 | hi1
          · rw [rowJ, tr_o] at hi1
            exact hTT ⟨v, Jv j, Jv i, a1, hi1.2, hi2.2⟩
          · rw [rowJ, tr_i] at hi1
            exact hTT ⟨v, Jv i, Jv j, hi2.2, hi1.2, a1⟩
        · intro i hi1 hi2
          rw [rowJ, tr_i] at hi1
          rw [tr_i] at hi2
          exact hTT ⟨Jv i, v, Jv j, hi2.2, a1, hi1.2⟩
    · by_cases a2 : D.arc (Jv j) v
      · rw [tr_succ_i a2] at ih'
        apply List.mem_append_right
        apply List.mem_append_right
        rw [ite_eq_left]
        · exact ih'
        · rw [Bool.and_eq_true, Bool.and_eq_true]
          refine ⟨⟨h2 j hjn a2, z_land ?_⟩, z_land ?_⟩
          · intro i hi1 hi2
            rw [lor_tb, Bool.or_eq_true] at hi1
            rw [tr_i] at hi2
            rcases hi1 with hi1 | hi1
            · rw [rowJ, tr_o] at hi1
              exact hTT ⟨Jv j, Jv i, v, hi1.2, hi2.2, a2⟩
            · rw [rowJ, tr_i] at hi1
              exact hTT ⟨Jv i, Jv j, v, hi1.2, a2, hi2.2⟩
          · intro i hi1 hi2
            rw [rowJ, tr_o] at hi1
            rw [tr_o] at hi2
            exact hTT ⟨Jv j, v, Jv i, a2, hi2.2, hi1.2⟩
      · have a3 : NA D v (Jv j) := ⟨a1, a2⟩
        rw [tr_succ_n a3] at ih'
        apply List.mem_append_left
        rw [ite_eq_left]
        · exact ih'
        · rw [Bool.and_eq_true]
          refine ⟨h0 j hjn a3, ?_⟩
          cases hc : chk3
          · rfl
          · rw [Bool.not_true, Bool.false_or]
            apply z_land
            intro i hi1 hi2
            rw [rowJ, tr_n] at hi1
            rw [tr_n] at hi2
            exact h3 hc i j hi1.1 hjn hi1.2 hi2.2 a3

/-! ### Step 1 -/

/-- What the fixed pairs say (both types): `0` is adjacent to no `J j`, and the pairs fixed
inside `J`. -/
structure JFix (D : OGraph (Fin 14)) : Prop where
  u : ∀ j, j < 8 → NA D 0 (Jv j)
  a01 : D.arc (Jv 0) (Jv 1)
  a02 : D.arc (Jv 0) (Jv 2)
  a30 : D.arc (Jv 3) (Jv 0)
  a40 : D.arc (Jv 4) (Jv 0)
  n05 : NA D (Jv 5) (Jv 0)
  n06 : NA D (Jv 6) (Jv 0)
  n07 : NA D (Jv 7) (Jv 0)
  n12 : NA D (Jv 2) (Jv 1)
  n34 : NA D (Jv 4) (Jv 3)

theorem allow0 {D : OGraph (Fin 14)} (F : JFix D) (v j : Nat) (hv : v < 8) (hj : j < v)
    (h : NA D (Jv v) (Jv j)) : allowJ v j 0 = true := by
  interval_cases v <;> interval_cases j <;>
    first
      | rfl | exact absurd F.a01 h.2 | exact absurd F.a02 h.2 | exact absurd F.a30 h.1
      | exact absurd F.a40 h.1

theorem allow1 {D : OGraph (Fin 14)} (F : JFix D) (v j : Nat) (hv : v < 8) (hj : j < v)
    (h : D.arc (Jv v) (Jv j)) : allowJ v j 1 = true := by
  interval_cases v <;> interval_cases j <;>
    first
      | rfl | exact absurd h (D.asymm _ _ F.a01) | exact absurd h (D.asymm _ _ F.a02)
      | exact absurd h F.n05.1 | exact absurd h F.n06.1 | exact absurd h F.n07.1
      | exact absurd h F.n12.1 | exact absurd h F.n34.1

theorem allow2 {D : OGraph (Fin 14)} (F : JFix D) (v j : Nat) (hv : v < 8) (hj : j < v)
    (h : D.arc (Jv j) (Jv v)) : allowJ v j 2 = true := by
  interval_cases v <;> interval_cases j <;>
    first
      | rfl | exact absurd h (D.asymm _ _ F.a30) | exact absurd h (D.asymm _ _ F.a40)
      | exact absurd h F.n05.2 | exact absurd h F.n06.2 | exact absurd h F.n07.2
      | exact absurd h F.n12.2 | exact absurd h F.n34.2

theorem jsearch_true (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4) (F : JFix D)
    (k : List Row → Bool) (hk : k (rowsJ D) = true) :
    ∀ m v, v + m = 8 → jsearch k m v ((List.range v).map (rowJ D)) = true := by
  intro m
  induction m with
  | zero =>
    intro v hv
    have : v = 8 := by omega
    subst this
    exact hk
  | succ m ih =>
    intro v hv
    have hv8 : v < 8 := by omega
    rw [jsearch, List.any_eq_true]
    refine ⟨rowJ D v, ?_, ?_⟩
    · have := gen_mem D hTT true (allowJ v) (Jv v) v
        (fun j hj h => allow0 F v j hv8 hj h) (fun j hj h => allow1 F v j hv8 hj h)
        (fun j hj h => allow2 F v j hv8 hj h)
        (fun _ i j hij hjv n1 n2 n3 =>
          indep4 D hI 0 (Jv i) (Jv j) (Jv v)
            (lt6_ne (by decide) (by omega)) (lt6_ne (by decide) (by omega))
            (lt6_ne (by decide) (by omega))
            (Jv_ne (by omega) (by omega) (by omega)) (Jv_ne (by omega) (by omega) (by omega))
            (Jv_ne (by omega) (by omega) (by omega))
            (F.u i (by omega)) (F.u j (by omega)) (F.u v hv8) n1.symm n2.symm n3.symm)
        v 0 (by omega)
      rw [List.range_eq_range']
      exact this
    · have := ih (v + 1) (by omega)
      rw [List.range_succ, List.map_append] at this
      exact this

theorem rowsEq_eq : ∀ {a b : List Row}, rowsEq a b = true → a = b := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons _ _ => simp [rowsEq] at h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => simp [rowsEq] at h
    | cons y ys =>
      rw [rowsEq, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rw [rowEq, Bool.and_eq_true, Bool.and_eq_true] at h1
      have e1 := Nat.eq_of_beq_eq_true h1.1.1
      have e2 := Nat.eq_of_beq_eq_true h1.1.2
      have e3 := Nat.eq_of_beq_eq_true h1.2
      have : x = y := by
        cases x; cases y; simp only [Row.mk.injEq]; exact ⟨e1, e2, e3⟩
      rw [this, ih h2]

/-- The table of `D` on `J` is one of the 24 tables. -/
theorem rowsJ_mem (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4) (F : JFix D) : rowsJ D ∈ Js := by
  by_contra hnot
  have hk : (fun rows => !(Js.any fun J => rowsEq rows J)) (rowsJ D) = true := by
    show (!(Js.any fun J => rowsEq (rowsJ D) J)) = true
    cases h : (Js.any fun J => rowsEq (rowsJ D) J)
    · rfl
    · obtain ⟨J, hJ, he⟩ := List.any_eq_true.1 h
      exact absurd (rowsEq_eq he ▸ hJ) hnot
  have h1 := jsearch_true D hTT hI F (fun rows => !(Js.any fun J => rowsEq rows J)) hk 7 1 rfl
  have h2 := covered_Js
  unfold covered at h2
  have h3 : (List.range 1).map (rowJ D) = [row0] := rfl
  rw [h3] at h1
  rw [h1] at h2
  exact Bool.false_ne_true h2

/-! ### Step 2 -/

theorem att_mem (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT) (v : Fin 14) :
    att D v ∈ gen false allowAll (rowsJ D) 0 row0 := by
  have := gen_mem D hTT false allowAll v 8 (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun h => Bool.noConfusion h) 8 0 rfl
  rw [rowsJ, List.range_eq_range']
  exact this

theorem nonpair_spec (D : OGraph (Fin 14)) (M : Nat) :
    ∀ m j, nonpair M ((List.range' j m).map (rowJ D)) j = true →
      ∃ k, k < j + m ∧ M.testBit k = true ∧ Nat.land (rowJ D k).n M ≠ 0 := by
  intro m
  induction m with
  | zero => intro j h; simp [nonpair] at h
  | succ m ih =>
    intro j h
    rw [List.range'_succ, List.map_cons, nonpair, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.and_eq_true] at h
      refine ⟨j, by omega, by rw [← tb_eq]; exact h.1, ?_⟩
      intro h0
      rw [h0] at h
      exact Bool.false_ne_true h.2
    · obtain ⟨k, hk, r⟩ := ih (j + 1) h
      exact ⟨k, by omega, r⟩

theorem cn_true (D : OGraph (Fin 14))
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4) (v w : Fin 14)
    (hv : v.val < 6) (hw : w.val < 6) (hvw : v ≠ w) (hna : NA D v w) :
    cn (rowsJ D) (att D v) (att D w) = true := by
  unfold cn
  cases hc : nonpair (Nat.land (att D v).n (att D w).n) (rowsJ D) 0
  · rfl
  · exfalso
    rw [rowsJ, List.range_eq_range'] at hc
    obtain ⟨k, hk, hMk, hne⟩ := nonpair_spec D _ 8 0 hc
    obtain ⟨i, hi1, hi2⟩ := land_bit hne
    rw [rowJ, tr_n] at hi1
    obtain ⟨b1, b2⟩ := land_tb hMk
    obtain ⟨b3, b4⟩ := land_tb hi2
    rw [att, tr_n] at b1 b2 b3 b4
    have hk8 : k < 8 := by omega
    have hi8 : i < 8 := by omega
    exact indep4 D hI v w (Jv i) (Jv k) hvw (lt6_ne hv hi8) (lt6_ne hv hk8) (lt6_ne hw hi8)
      (lt6_ne hw hk8) (Jv_ne hi8 hk8 (by omega)) hna b3.2 b1.2 b4.2 b2.2 hi1.2.symm

theorem cf_true (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT) (p q : Fin 14) (h : D.arc p q) :
    cf (att D p) (att D q) = true := by
  unfold cf
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨z_land ?_, z_land ?_⟩, z_land ?_⟩
  · intro i h1 h2
    rw [att, tr_o] at h1 h2
    exact hTT ⟨p, q, Jv i, h, h2.2, h1.2⟩
  · intro i h1 h2
    rw [att, tr_i] at h1 h2
    exact hTT ⟨Jv i, p, q, h1.2, h, h2.2⟩
  · intro i h1 h2
    rw [att, tr_o] at h1
    rw [att, tr_i] at h2
    exact hTT ⟨p, Jv i, q, h1.2, h2.2, h⟩

/-- Between the big vertex `x` and the small vertex `y`, the arc that `dir` forbids is absent. -/
def DirOK (D : OGraph (Fin 14)) (dir : Bool) (x y : Fin 14) : Prop :=
  (dir = true → ¬ D.arc y x) ∧ (dir = false → ¬ D.arc x y)

theorem xok_true (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4) (dir : Bool) (x y : Fin 14)
    (hx : x.val < 6) (hy : y.val < 6) (hxy : x ≠ y) (hd : DirOK D dir x y) :
    xok (rowsJ D) dir (att D x) (att D y) = true := by
  unfold xok cross
  rw [Bool.or_eq_true]
  cases dir
  · by_cases h : D.arc y x
    · left; exact cf_true D hTT y x h
    · right; exact cn_true D hI x y hx hy hxy ⟨hd.2 rfl, h⟩
  · by_cases h : D.arc x y
    · left; exact cf_true D hTT x y h
    · right; exact cn_true D hI x y hx hy hxy ⟨h, hd.1 rfl⟩

theorem le_total' (a b : Row) : le a b = true ∨ le b a = true := by
  unfold le
  rw [Nat.ble_eq, Nat.ble_eq]
  omega

theorem le_trans' {a b c : Row} (h1 : le a b = true) (h2 : le b c = true) : le a c = true := by
  exact Nat.ble_eq_true_of_le (Nat.le_trans (Nat.le_of_ble_eq_true h1) (Nat.le_of_ble_eq_true h2))

/-- The hypotheses of step 2 on three big vertices and two small ones, apart from the order. -/
structure Five (D : OGraph (Fin 14)) (dir : Bool) (x1 x2 x3 y1 y2 : Fin 14) : Prop where
  hx1 : x1.val < 6
  hx2 : x2.val < 6
  hx3 : x3.val < 6
  hy1 : y1.val < 6
  hy2 : y2.val < 6
  d12 : x1 ≠ x2
  d13 : x1 ≠ x3
  d23 : x2 ≠ x3
  dy : y1 ≠ y2
  n12 : NA D x1 x2
  n13 : NA D x1 x3
  n23 : NA D x2 x3
  ny : NA D y1 y2
  c : ∀ x, x = x1 ∨ x = x2 ∨ x = x3 → ∀ y, y = y1 ∨ y = y2 → x ≠ y ∧ DirOK D dir x y

theorem stage2_sorted (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4) (dir : Bool)
    (x1 x2 x3 y1 y2 : Fin 14) (H : Five D dir x1 x2 x3 y1 y2)
    (l12 : le (att D x1) (att D x2) = true) (l23 : le (att D x2) (att D x3) = true) :
    stage2 dir (rowsJ D) = true := by
  have c12 := cn_true D hI x1 x2 H.hx1 H.hx2 H.d12 H.n12
  have c13 := cn_true D hI x1 x3 H.hx1 H.hx3 H.d13 H.n13
  have c23 := cn_true D hI x2 x3 H.hx2 H.hx3 H.d23 H.n23
  have cy := cn_true D hI y1 y2 H.hy1 H.hy2 H.dy H.ny
  have l13 := le_trans' l12 l23
  have zt : z (Nat.land (Nat.land (att D x1).n (att D x2).n) (att D x3).n) = true := by
    apply z_land
    intro i h1 h2
    obtain ⟨b1, b2⟩ := land_tb h1
    rw [att, tr_n] at b1 b2 h2
    have hi := b1.1
    exact indep4 D hI x1 x2 x3 (Jv i) H.d12 H.d13 (lt6_ne H.hx1 hi) H.d23 (lt6_ne H.hx2 hi)
      (lt6_ne H.hx3 hi) H.n12 H.n13 b1.2 H.n23 b2.2 h2.2
  have xo : ∀ x, x = x1 ∨ x = x2 ∨ x = x3 → ∀ y, y = y1 ∨ y = y2 →
      xok (rowsJ D) dir (att D x) (att D y) = true := by
    intro x hx y hy
    have hxv : x.val < 6 := by
      rcases hx with rfl | rfl | rfl
      · exact H.hx1
      · exact H.hx2
      · exact H.hx3
    have hyv : y.val < 6 := by
      rcases hy with rfl | rfl
      · exact H.hy1
      · exact H.hy2
    exact xok_true D hTT hI dir x y hxv hyv (H.c x hx y hy).1 (H.c x hx y hy).2
  have my : ∀ y, y = y1 ∨ y = y2 → att D y ∈
      (gen false allowAll (rowsJ D) 0 row0).filter (fun q =>
        xok (rowsJ D) dir (att D x1) q && xok (rowsJ D) dir (att D x2) q &&
          xok (rowsJ D) dir (att D x3) q) := by
    intro y hy
    refine List.mem_filter.2 ⟨att_mem D hTT y, ?_⟩
    rw [xo x1 (Or.inl rfl) y hy, xo x2 (Or.inr (Or.inl rfl)) y hy,
      xo x3 (Or.inr (Or.inr rfl)) y hy]
    rfl
  unfold stage2
  dsimp only
  rw [List.any_eq_true]
  refine ⟨att D x1, att_mem D hTT x1, ?_⟩
  rw [List.any_eq_true]
  refine ⟨att D x2, List.mem_filter.2 ⟨att_mem D hTT x2, by rw [l12, c12]; rfl⟩, ?_⟩
  rw [List.any_eq_true]
  refine ⟨att D x3, List.mem_filter.2 ⟨att_mem D hTT x3, by rw [l13, c13]; rfl⟩, ?_⟩
  rw [l23, c23, zt, Bool.true_and, Bool.true_and, Bool.true_and, List.any_eq_true]
  refine ⟨att D y1, my y1 (Or.inl rfl), ?_⟩
  rw [List.any_eq_true]
  exact ⟨att D y2, my y2 (Or.inr rfl), cy⟩

theorem stage2_true (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4) (dir : Bool)
    (x1 x2 x3 y1 y2 : Fin 14) (H : Five D dir x1 x2 x3 y1 y2) :
    stage2 dir (rowsJ D) = true := by
  have H132 : Five D dir x1 x3 x2 y1 y2 :=
    { H with hx2 := H.hx3, hx3 := H.hx2, d12 := H.d13, d13 := H.d12, d23 := H.d23.symm,
             n12 := H.n13, n13 := H.n12, n23 := H.n23.symm,
             c := fun x hx => H.c x (by tauto) }
  have H213 : Five D dir x2 x1 x3 y1 y2 :=
    { H with hx1 := H.hx2, hx2 := H.hx1, d12 := H.d12.symm, d13 := H.d23, d23 := H.d13,
             n12 := H.n12.symm, n13 := H.n23, n23 := H.n13,
             c := fun x hx => H.c x (by tauto) }
  have H231 : Five D dir x2 x3 x1 y1 y2 :=
    { H with hx1 := H.hx2, hx2 := H.hx3, hx3 := H.hx1, d12 := H.d23, d13 := H.d12.symm,
             d23 := H.d13.symm, n12 := H.n23, n13 := H.n12.symm, n23 := H.n13.symm,
             c := fun x hx => H.c x (by tauto) }
  have H312 : Five D dir x3 x1 x2 y1 y2 :=
    { H with hx1 := H.hx3, hx2 := H.hx1, hx3 := H.hx2, d12 := H.d13.symm, d13 := H.d23.symm,
             d23 := H.d12, n12 := H.n13.symm, n13 := H.n23.symm, n23 := H.n12,
             c := fun x hx => H.c x (by tauto) }
  have H321 : Five D dir x3 x2 x1 y1 y2 :=
    { H with hx1 := H.hx3, hx3 := H.hx1, d12 := H.d23.symm, d13 := H.d13.symm,
             d23 := H.d12.symm, n12 := H.n23.symm, n13 := H.n13.symm, n23 := H.n12.symm,
             c := fun x hx => H.c x (by tauto) }
  rcases le_total' (att D x1) (att D x2) with a | a <;>
  rcases le_total' (att D x2) (att D x3) with b | b <;>
  rcases le_total' (att D x1) (att D x3) with c | c
  · exact stage2_sorted D hTT hI dir _ _ _ _ _ H a b
  · exact stage2_sorted D hTT hI dir _ _ _ _ _ H a b
  · exact stage2_sorted D hTT hI dir _ _ _ _ _ H132 c b
  · exact stage2_sorted D hTT hI dir _ _ _ _ _ H312 c a
  · exact stage2_sorted D hTT hI dir _ _ _ _ _ H213 a c
  · exact stage2_sorted D hTT hI dir _ _ _ _ _ H231 b c
  · exact stage2_sorted D hTT hI dir _ _ _ _ _ H321 b a
  · exact stage2_sorted D hTT hI dir _ _ _ _ _ H321 b a

/-- The pairs fixed for both types. -/
def fixedJ : List (Fin 14 × Fin 14 × PS) :=
  [(0, 6, .non), (0, 7, .non), (0, 8, .non), (0, 9, .non), (0, 10, .non), (0, 11, .non),
   (0, 12, .non), (0, 13, .non),
   (6, 7, .fwd), (6, 8, .fwd), (6, 9, .bwd), (6, 10, .bwd),
   (6, 11, .non), (6, 12, .non), (6, 13, .non), (7, 8, .non), (9, 10, .non)]

theorem fixedJ_sub32 : ∀ e ∈ fixedJ, e ∈ fixed32 := by decide

theorem fixedJ_sub23 : ∀ e ∈ fixedJ, e ∈ fixed23 := by decide

theorem jfix_of (D : OGraph (Fin 14)) (h : ∀ e ∈ fixedJ, Agree D e.1 e.2.1 e.2.2) :
    JFix D := by
  have e0 : NA D 0 (Jv 0) := h (0, 6, .non) (by decide)
  have e1 : NA D 0 (Jv 1) := h (0, 7, .non) (by decide)
  have e2 : NA D 0 (Jv 2) := h (0, 8, .non) (by decide)
  have e3 : NA D 0 (Jv 3) := h (0, 9, .non) (by decide)
  have e4 : NA D 0 (Jv 4) := h (0, 10, .non) (by decide)
  have e5 : NA D 0 (Jv 5) := h (0, 11, .non) (by decide)
  have e6 : NA D 0 (Jv 6) := h (0, 12, .non) (by decide)
  have e7 : NA D 0 (Jv 7) := h (0, 13, .non) (by decide)
  have n05 : NA D (Jv 0) (Jv 5) := h (6, 11, .non) (by decide)
  have n06 : NA D (Jv 0) (Jv 6) := h (6, 12, .non) (by decide)
  have n07 : NA D (Jv 0) (Jv 7) := h (6, 13, .non) (by decide)
  have n12 : NA D (Jv 1) (Jv 2) := h (7, 8, .non) (by decide)
  have n34 : NA D (Jv 3) (Jv 4) := h (9, 10, .non) (by decide)
  exact
    { u := by
        intro j hj
        interval_cases j
        · exact e0
        · exact e1
        · exact e2
        · exact e3
        · exact e4
        · exact e5
        · exact e6
        · exact e7
      a01 := h (6, 7, .fwd) (by decide)
      a02 := h (6, 8, .fwd) (by decide)
      a30 := h (6, 9, .bwd) (by decide)
      a40 := h (6, 10, .bwd) (by decide)
      n05 := n05.symm
      n06 := n06.symm
      n07 := n07.symm
      n12 := n12.symm
      n34 := n34.symm }

end Erdos112.K

namespace Erdos112.Search

open Erdos112 Erdos112.K

/-- No `{I_4, L_3}`-free oriented graph on `Fin 14` agrees with the fixed pairs of type (3,2).
Kernel-checked: uses `covered_Js` and `all32`. -/
theorem no_graph32 (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4)
    (h : ∀ e ∈ fixed32, Agree D e.1 e.2.1 e.2.2) : False := by
  have F := jfix_of D (fun e he => h e (fixedJ_sub32 e he))
  have o1 : D.arc 0 1 := h (0, 1, .fwd) (by decide)
  have o2 : D.arc 0 2 := h (0, 2, .fwd) (by decide)
  have o3 : D.arc 0 3 := h (0, 3, .fwd) (by decide)
  have i4 : D.arc 4 0 := h (0, 4, .bwd) (by decide)
  have i5 : D.arc 5 0 := h (0, 5, .bwd) (by decide)
  have n12 : NA D 1 2 := h (1, 2, .non) (by decide)
  have n13 : NA D 1 3 := h (1, 3, .non) (by decide)
  have n23 : NA D 2 3 := h (2, 3, .non) (by decide)
  have n45 : NA D 4 5 := h (4, 5, .non) (by decide)
  have H : Five D true 1 2 3 4 5 :=
    { hx1 := by decide, hx2 := by decide, hx3 := by decide, hy1 := by decide, hy2 := by decide
      d12 := by decide, d13 := by decide, d23 := by decide, dy := by decide
      n12 := n12, n13 := n13, n23 := n23, ny := n45
      c := by
        rintro x (rfl | rfl | rfl) y (rfl | rfl) <;>
          refine ⟨by decide, fun _ ha => ?_, fun hf => Bool.noConfusion hf⟩ <;>
          first
            | exact hTT ⟨_, 0, _, i4, o1, ha⟩ | exact hTT ⟨_, 0, _, i4, o2, ha⟩
            | exact hTT ⟨_, 0, _, i4, o3, ha⟩ | exact hTT ⟨_, 0, _, i5, o1, ha⟩
            | exact hTT ⟨_, 0, _, i5, o2, ha⟩ | exact hTT ⟨_, 0, _, i5, o3, ha⟩ }
  have hs := stage2_true D hTT hI true 1 2 3 4 5 H
  rw [all32 _ (rowsJ_mem D hTT hI F)] at hs
  exact Bool.false_ne_true hs

/-- No `{I_4, L_3}`-free oriented graph on `Fin 14` agrees with the fixed pairs of type (2,3).
Kernel-checked: uses `covered_Js` and `all23`. -/
theorem no_graph23 (D : OGraph (Fin 14)) (hTT : ¬ D.HasTT)
    (hI : ∀ T : Finset (Fin 14), D.IsIndep T → T.card ≠ 4)
    (h : ∀ e ∈ fixed23, Agree D e.1 e.2.1 e.2.2) : False := by
  have F := jfix_of D (fun e he => h e (fixedJ_sub23 e he))
  have o1 : D.arc 0 1 := h (0, 1, .fwd) (by decide)
  have o2 : D.arc 0 2 := h (0, 2, .fwd) (by decide)
  have i3 : D.arc 3 0 := h (0, 3, .bwd) (by decide)
  have i4 : D.arc 4 0 := h (0, 4, .bwd) (by decide)
  have i5 : D.arc 5 0 := h (0, 5, .bwd) (by decide)
  have n12 : NA D 1 2 := h (1, 2, .non) (by decide)
  have n34 : NA D 3 4 := h (3, 4, .non) (by decide)
  have n35 : NA D 3 5 := h (3, 5, .non) (by decide)
  have n45 : NA D 4 5 := h (4, 5, .non) (by decide)
  have H : Five D false 3 4 5 1 2 :=
    { hx1 := by decide, hx2 := by decide, hx3 := by decide, hy1 := by decide, hy2 := by decide
      d12 := by decide, d13 := by decide, d23 := by decide, dy := by decide
      n12 := n34, n13 := n35, n23 := n45, ny := n12
      c := by
        rintro x (rfl | rfl | rfl) y (rfl | rfl) <;>
          refine ⟨by decide, fun hf => Bool.noConfusion hf, fun _ ha => ?_⟩ <;>
          first
            | exact hTT ⟨_, 0, _, i3, o1, ha⟩ | exact hTT ⟨_, 0, _, i3, o2, ha⟩
            | exact hTT ⟨_, 0, _, i4, o1, ha⟩ | exact hTT ⟨_, 0, _, i4, o2, ha⟩
            | exact hTT ⟨_, 0, _, i5, o1, ha⟩ | exact hTT ⟨_, 0, _, i5, o2, ha⟩ }
  have hs := stage2_true D hTT hI false 3 4 5 1 2 H
  rw [all23 _ (rowsJ_mem D hTT hI F)] at hs
  exact Bool.false_ne_true hs

end Erdos112.Search
