module

public import Erdos112.LemmaB

@[expose] public section

/-!
# The upper bound `k(6,3) ≤ 32` (paper, Section 4)

`bound_4_15` and `bound_5_23` are the values `k(4,3) ≤ 15` and `k(5,3) ≤ 23` that the paper
cites from Ihringer, Rajendraprasad and Weinert (Theorem 3 of the paper); they are proved
here by the same degree-sum argument, so that nothing is taken from the literature.
`lemmaA` is Lemma 9 and `bound_6_32` is Theorem 10.

Arc counts appear doubled: `E D X X` is `2 e(X)`. Lemma 9 is stated as `2 e(H) ≥ 147`, which
is the same as `e(H) ≥ 74`.
-/

namespace Erdos112

open scoped Classical

theorem sum_le_of_le {V : Type} {s : Finset V} {f : V → ℕ} {n : ℕ} (h : ∀ x ∈ s, f x ≤ n) :
    ∑ x ∈ s, f x ≤ s.card * n := by
  calc ∑ x ∈ s, f x ≤ ∑ _x ∈ s, n := Finset.sum_le_sum h
    _ = s.card * n := by simp

theorem le_sum_of_le {V : Type} {s : Finset V} {f : V → ℕ} {n : ℕ} (h : ∀ x ∈ s, n ≤ f x) :
    s.card * n ≤ ∑ x ∈ s, f x := by
  calc s.card * n = ∑ _x ∈ s, n := by simp
    _ ≤ ∑ x ∈ s, f x := Finset.sum_le_sum h

theorem OGraph.deg_le {V : Type} (D : OGraph V) (hTT : ¬ D.HasTT) {S : Finset V} {n : ℕ}
    (hS : D.NoIndep S n) (x : V) : D.deg S x + 2 ≤ 2 * n := by
  have h1 := D.card_outN_lt hTT hS x
  have h2 := D.card_inN_lt hTT hS x
  rw [D.deg_eq]; omega

/-- `k(4,3) ≤ 15` (paper, Theorem 3; Observation 4.1 of Ihringer, Rajendraprasad, Weinert). -/
theorem bound_4_15 : Bound 4 15 := by
  apply bound_of_exact
  intro V D hTT S hS hc
  obtain ⟨v, hv⟩ : S.Nonempty := by rw [← Finset.card_pos]; omega
  have h1 := D.card_split hv
  have h2 := D.card_outN_lt hTT hS v
  have h3 := D.card_inN_lt hTT hS v
  have hC : D.NoIndep (D.nonN S v) 3 := D.noIndep_nonN hv hS
  have h4 := bound_3_9 V D hTT _ hC
  have hC8 : (D.nonN S v).card = 8 := by omega
  have hE : (D.nonN S v).card * 4 ≤ D.E (D.nonN S v) (D.nonN S v) := by
    unfold OGraph.E
    exact le_sum_of_le (fun c hc' => by
      have := D.type8 hTT hC hC8 c hc'
      rw [D.deg_eq]; omega)
  have hEo := D.count_a hTT hS (D.outN_subset S v) (D.nonN_subset S v) (D.indep_outN hTT S v)
    (D.disjoint_outN_nonN S v) (by omega)
  have hEi := D.count_a hTT hS (D.inN_subset S v) (D.nonN_subset S v) (D.indep_inN hTT S v)
    (D.disjoint_inN_nonN S v) (by omega)
  have hsum := D.degsum hv
  have hup : ∑ c ∈ D.nonN S v, D.deg S c ≤ (D.nonN S v).card * 6 :=
    sum_le_of_le (fun c _ => by have := D.deg_le hTT hS c; omega)
  omega

/-- `k(5,3) ≤ 23` (paper, Theorem 3; Observation 4.2 of Ihringer, Rajendraprasad, Weinert).
Proved here with Lemma 8. -/
theorem bound_5_23 : Bound 5 23 := by
  apply bound_of_exact
  intro V D hTT S hS hc
  obtain ⟨v, hv⟩ : S.Nonempty := by rw [← Finset.card_pos]; omega
  have h1 := D.card_split hv
  have h2 := D.card_outN_lt hTT hS v
  have h3 := D.card_inN_lt hTT hS v
  have hC : D.NoIndep (D.nonN S v) 4 := D.noIndep_nonN hv hS
  have h4 := bound_4_15 V D hTT _ hC
  have hC14 : (D.nonN S v).card = 14 := by omega
  have hE : (D.nonN S v).card * 6 ≤ D.E (D.nonN S v) (D.nonN S v) := by
    unfold OGraph.E
    exact le_sum_of_le (fun c hc' => (lemmaB D hTT hC hC14 c hc').ge)
  have hEo := D.count_a hTT hS (D.outN_subset S v) (D.nonN_subset S v) (D.indep_outN hTT S v)
    (D.disjoint_outN_nonN S v) (by omega)
  have hEi := D.count_a hTT hS (D.inN_subset S v) (D.nonN_subset S v) (D.indep_inN hTT S v)
    (D.disjoint_inN_nonN S v) (by omega)
  have hsum := D.degsum hv
  have hup : ∑ c ∈ D.nonN S v, D.deg S c ≤ (D.nonN S v).card * 8 :=
    sum_le_of_le (fun c _ => by have := D.deg_le hTT hS c; omega)
  omega

/-- **Lemma 9 of the paper.** Every `{I_5, L_3}`-free oriented graph on 21 vertices has at
least 74 arcs; stated as `2 e(H) ≥ 147`. -/
theorem lemmaA {V : Type} (D : OGraph V) (hTT : ¬ D.HasTT) {S : Finset V}
    (hS : D.NoIndep S 5) (hc : S.card = 21) : 147 ≤ D.E S S := by
  have hdeg : ∀ w ∈ S, 6 ≤ D.deg S w := by
    intro w hw
    have h1 := D.card_split hw
    have h2 := D.card_outN_lt hTT hS w
    have h3 := D.card_inN_lt hTT hS w
    have h4 := bound_4_15 V D hTT _ (D.noIndep_nonN hw hS)
    rw [D.deg_eq]; omega
  have hES : D.E S S = ∑ y ∈ S, D.deg S y := rfl
  by_cases hall : ∀ w ∈ S, 7 ≤ D.deg S w
  · have h7 : S.card * 7 ≤ ∑ y ∈ S, D.deg S y := le_sum_of_le hall
    omega
  · push Not at hall
    obtain ⟨u, hu, hu7⟩ := hall
    have hu6 := hdeg u hu
    have h1 := D.card_split hu
    have h2 := D.card_outN_lt hTT hS u
    have h3 := D.card_inN_lt hTT hS u
    have hdu := D.deg_eq S u
    have hJ : D.NoIndep (D.nonN S u) 4 := D.noIndep_nonN hu hS
    have hJ14 : (D.nonN S u).card = 14 := by omega
    have hEJ : (D.nonN S u).card * 6 ≤ D.E (D.nonN S u) (D.nonN S u) := by
      unfold OGraph.E
      exact le_sum_of_le (fun c hc' => (lemmaB D hTT hJ hJ14 c hc').ge)
    have hsplit : ∑ y ∈ S, D.deg S y = D.deg S u + ∑ y ∈ D.outN S u, D.deg S y
        + ∑ y ∈ D.inN S u, D.deg S y + ∑ y ∈ D.nonN S u, D.deg S y := D.sum_split hu _
    have hP : (D.outN S u).card * 6 ≤ ∑ y ∈ D.outN S u, D.deg S y :=
      le_sum_of_le (fun y hy => hdeg y (D.outN_subset S u hy))
    have hQ : (D.inN S u).card * 6 ≤ ∑ y ∈ D.inN S u, D.deg S y :=
      le_sum_of_le (fun y hy => hdeg y (D.inN_subset S u hy))
    have hsum : ∑ c ∈ D.nonN S u, D.deg S c = D.E (D.outN S u) (D.nonN S u)
        + D.E (D.inN S u) (D.nonN S u) + D.E (D.nonN S u) (D.nonN S u) := D.degsum hu
    have hs : 22 ≤ D.E (D.outN S u) (D.nonN S u) + D.E (D.inN S u) (D.nonN S u) := by
      have hty : ((D.outN S u).card = 3 ∧ (D.inN S u).card = 3)
          ∨ ((D.outN S u).card = 4 ∧ (D.inN S u).card = 2)
          ∨ ((D.outN S u).card = 2 ∧ (D.inN S u).card = 4) := by omega
      rcases hty with ⟨ho, hi⟩ | ⟨ho, hi⟩ | ⟨ho, hi⟩
      · -- type (3,3): Lemma 4 (b) twice
        have a := D.count_b hTT hS (D.outN_subset S u) (D.nonN_subset S u)
          (D.indep_outN hTT S u) (D.disjoint_outN_nonN S u) (by omega)
        have b := D.count_b hTT hS (D.inN_subset S u) (D.nonN_subset S u)
          (D.indep_inN hTT S u) (D.disjoint_inN_nonN S u) (by omega)
        omega
      · -- type (4,2): Lemma 4 (a) and (c)
        have a := D.count_a hTT hS (D.outN_subset S u) (D.nonN_subset S u)
          (D.indep_outN hTT S u) (D.disjoint_outN_nonN S u) (by omega)
        have b := D.count_c hTT hS (D.inN_subset S u) (D.nonN_subset S u)
          (D.indep_inN hTT S u) (D.disjoint_inN_nonN S u) (by omega)
        omega
      · -- type (2,4): Lemma 4 (c) and (a)
        have a := D.count_c hTT hS (D.outN_subset S u) (D.nonN_subset S u)
          (D.indep_outN hTT S u) (D.disjoint_outN_nonN S u) (by omega)
        have b := D.count_a hTT hS (D.inN_subset S u) (D.nonN_subset S u)
          (D.indep_inN hTT S u) (D.disjoint_inN_nonN S u) (by omega)
        omega
    omega

/-- **Theorem 10 of the paper**, in relative form: a vertex set with no independent set of 6
vertices, in an oriented graph with no transitive triangle, has fewer than 32 vertices. -/
theorem bound_6_32 : Bound 6 32 := by
  apply bound_of_exact
  intro V D hTT S hS hc
  have hdeg : ∀ w ∈ S, 9 ≤ D.deg S w ∧ D.deg S w ≤ 10 := by
    intro w hw
    have h1 := D.card_split hw
    have h2 := D.card_outN_lt hTT hS w
    have h3 := D.card_inN_lt hTT hS w
    have h4 := bound_5_23 V D hTT _ (D.noIndep_nonN hw hS)
    rw [D.deg_eq]; omega
  by_cases hA : ∃ v ∈ S, D.deg S v = 10
  · -- Case A: a vertex of degree 10
    obtain ⟨v, hv, hv10⟩ := hA
    have h1 := D.card_split hv
    have h2 := D.card_outN_lt hTT hS v
    have h3 := D.card_inN_lt hTT hS v
    have hdv := D.deg_eq S v
    have hC : D.NoIndep (D.nonN S v) 5 := D.noIndep_nonN hv hS
    have hC21 : (D.nonN S v).card = 21 := by omega
    have hE := lemmaA D hTT hC hC21
    have hEo := D.count_a hTT hS (D.outN_subset S v) (D.nonN_subset S v)
      (D.indep_outN hTT S v) (D.disjoint_outN_nonN S v) (by omega)
    have hEi := D.count_a hTT hS (D.inN_subset S v) (D.nonN_subset S v)
      (D.indep_inN hTT S v) (D.disjoint_inN_nonN S v) (by omega)
    have hsum : ∑ c ∈ D.nonN S v, D.deg S c = D.E (D.outN S v) (D.nonN S v)
        + D.E (D.inN S v) (D.nonN S v) + D.E (D.nonN S v) (D.nonN S v) := D.degsum hv
    have hup : ∑ c ∈ D.nonN S v, D.deg S c ≤ (D.nonN S v).card * 10 :=
      sum_le_of_le (fun c hc' => (hdeg c (D.nonN_subset S v hc')).2)
    omega
  · -- Case B: every vertex has degree 9
    push Not at hA
    have hall : ∀ w ∈ S, D.deg S w = 9 := fun w hw => by
      have a := hdeg w hw
      have b := hA w hw
      omega
    obtain ⟨v, hv⟩ : S.Nonempty := by rw [← Finset.card_pos]; omega
    have h1 := D.card_split hv
    have h2 := D.card_outN_lt hTT hS v
    have h3 := D.card_inN_lt hTT hS v
    have hdv := D.deg_eq S v
    have hv9 := hall v hv
    have hC : D.NoIndep (D.nonN S v) 5 := D.noIndep_nonN hv hS
    have hC22 : (D.nonN S v).card = 22 := by omega
    have hE : (D.nonN S v).card * 7 ≤ D.E (D.nonN S v) (D.nonN S v) := by
      unfold OGraph.E
      exact le_sum_of_le (fun c hc' => by
        have a1 := D.card_split hc'
        have a2 := D.card_outN_lt hTT hC c
        have a3 := D.card_inN_lt hTT hC c
        have a4 := bound_4_15 V D hTT _ (D.noIndep_nonN hc' hC)
        rw [D.deg_eq]; omega)
    have hs : 53 ≤ D.E (D.outN S v) (D.nonN S v) + D.E (D.inN S v) (D.nonN S v) := by
      have hty : ((D.outN S v).card = 5 ∧ (D.inN S v).card = 4)
          ∨ ((D.outN S v).card = 4 ∧ (D.inN S v).card = 5) := by omega
      rcases hty with ⟨ho, hi⟩ | ⟨ho, hi⟩
      · have a := D.count_a hTT hS (D.outN_subset S v) (D.nonN_subset S v)
          (D.indep_outN hTT S v) (D.disjoint_outN_nonN S v) (by omega)
        have b := D.count_b hTT hS (D.inN_subset S v) (D.nonN_subset S v)
          (D.indep_inN hTT S v) (D.disjoint_inN_nonN S v) (by omega)
        omega
      · have a := D.count_b hTT hS (D.outN_subset S v) (D.nonN_subset S v)
          (D.indep_outN hTT S v) (D.disjoint_outN_nonN S v) (by omega)
        have b := D.count_a hTT hS (D.inN_subset S v) (D.nonN_subset S v)
          (D.indep_inN hTT S v) (D.disjoint_inN_nonN S v) (by omega)
        omega
    have hsum : ∑ c ∈ D.nonN S v, D.deg S c = D.E (D.outN S v) (D.nonN S v)
        + D.E (D.inN S v) (D.nonN S v) + D.E (D.nonN S v) (D.nonN S v) := D.degsum hv
    have hup : ∑ c ∈ D.nonN S v, D.deg S c ≤ (D.nonN S v).card * 9 :=
      sum_le_of_le (fun c hc' => (hall c (D.nonN_subset S v hc')).le)
    omega

end Erdos112
