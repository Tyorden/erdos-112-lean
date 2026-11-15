import Erdos112.Defs

/-!
# Basic facts and the counting lemma (paper, Section 2)

All statements are made relative to a finite vertex set `S` inside an ambient oriented graph
with no transitive triangle. This replaces the paper's induced subgraphs `D[X]`: "`D[S]` is
`{I_n, L_3}`-free" becomes "`D` has no transitive triangle and `S` contains no independent
set of `n` vertices" (`NoIndep D S n`).

To avoid halving, arcs are counted through degree sums: `E D A X` is the sum over `x ∈ X` of
the number of neighbours of `x` in `A`. For disjoint `A`, `X` it is the paper's `e(A,X)`,
and `E D X X` is `2 e(X)`.
-/

namespace Erdos112

open scoped Classical

namespace OGraph

variable {V : Type} (D : OGraph V)

theorem arc_irrefl (x : V) : ¬ D.arc x x := fun h => D.asymm x x h h

theorem adj_symm {x y : V} : D.adj x y ↔ D.adj y x := by unfold adj; tauto

theorem adj_irrefl (x : V) : ¬ D.adj x x := by
  unfold adj; intro h; rcases h with h | h <;> exact D.arc_irrefl x h

theorem isIndep_mono {T T' : Finset V} (h : D.IsIndep T) (hs : T' ⊆ T) : D.IsIndep T' :=
  fun x hx y hy => h x (hs hx) y (hs hy)

theorem isIndep_union {A B : Finset V} (hA : D.IsIndep A) (hB : D.IsIndep B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, ¬ D.adj a b) : D.IsIndep (A ∪ B) := by
  intro x hx y hy hxy
  rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
  · exact hA x hx y hy hxy
  · exact hAB x hx y hy (Or.inl hxy)
  · exact hAB y hy x hx (Or.inr hxy)
  · exact hB x hx y hy hxy

/-- `S` contains no independent set of `n` (or more) vertices. -/
def NoIndep (S : Finset V) (n : ℕ) : Prop := ∀ T ⊆ S, D.IsIndep T → T.card < n

theorem noIndep_mono {S S' : Finset V} {n : ℕ} (hs : S' ⊆ S) (h : D.NoIndep S n) :
    D.NoIndep S' n := fun T hT => h T (hT.trans hs)

/-- Out-neighbours of `v` inside `S`: the paper's `N⁺(v)`. -/
noncomputable def outN (S : Finset V) (v : V) : Finset V := S.filter (fun y => D.arc v y)
/-- In-neighbours of `v` inside `S`: the paper's `N⁻(v)`. -/
noncomputable def inN (S : Finset V) (v : V) : Finset V := S.filter (fun y => D.arc y v)
/-- Vertices of `S` other than `v` that are not adjacent to `v`: the paper's `I(v)`. -/
noncomputable def nonN (S : Finset V) (v : V) : Finset V :=
  S.filter (fun y => y ≠ v ∧ ¬ D.adj v y)
/-- Number of neighbours of `x` in `S`; for `x ∈ S` this is the paper's degree `d(x)` in `D[S]`. -/
noncomputable def deg (S : Finset V) (x : V) : ℕ := (S.filter (fun y => D.adj x y)).card
/-- Sum over `x ∈ X` of the number of neighbours of `x` in `A`. -/
noncomputable def E (A X : Finset V) : ℕ := ∑ x ∈ X, D.deg A x

variable {D}

theorem mem_outN {S : Finset V} {v y : V} : y ∈ D.outN S v ↔ y ∈ S ∧ D.arc v y :=
  Finset.mem_filter
theorem mem_inN {S : Finset V} {v y : V} : y ∈ D.inN S v ↔ y ∈ S ∧ D.arc y v :=
  Finset.mem_filter
theorem mem_nonN {S : Finset V} {v y : V} : y ∈ D.nonN S v ↔ y ∈ S ∧ y ≠ v ∧ ¬ D.adj v y :=
  Finset.mem_filter

variable (D)

theorem outN_subset (S : Finset V) (v : V) : D.outN S v ⊆ S := Finset.filter_subset _ _
theorem inN_subset (S : Finset V) (v : V) : D.inN S v ⊆ S := Finset.filter_subset _ _
theorem nonN_subset (S : Finset V) (v : V) : D.nonN S v ⊆ S := Finset.filter_subset _ _

theorem disjoint_outN_nonN (S : Finset V) (v : V) : Disjoint (D.outN S v) (D.nonN S v) := by
  rw [Finset.disjoint_left]; intro y h1 h2
  exact (mem_nonN.1 h2).2.2 (Or.inl (mem_outN.1 h1).2)

theorem disjoint_inN_nonN (S : Finset V) (v : V) : Disjoint (D.inN S v) (D.nonN S v) := by
  rw [Finset.disjoint_left]; intro y h1 h2
  exact (mem_nonN.1 h2).2.2 (Or.inr (mem_inN.1 h1).2)

/-- Splitting a sum over `S` along `{v}`, `N⁺(v)`, `N⁻(v)`, `I(v)`. -/
theorem sum_split {S : Finset V} {v : V} (hv : v ∈ S) (f : V → ℕ) :
    ∑ y ∈ S, f y = f v + ∑ y ∈ D.outN S v, f y + ∑ y ∈ D.inN S v, f y
      + ∑ y ∈ D.nonN S v, f y := by
  have h1 : f v = ∑ y ∈ S, if y = v then f y else 0 := by
    simp [Finset.sum_ite_eq', hv]
  rw [h1]; unfold outN inN nonN
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hyv : y = v
  · subst hyv; simp [D.arc_irrefl, D.adj_irrefl]
  · by_cases h1 : D.arc v y
    · have := D.asymm v y h1; simp [hyv, h1, this, adj]
    · by_cases h2 : D.arc y v <;> simp [hyv, h1, h2, adj]

theorem card_split {S : Finset V} {v : V} (hv : v ∈ S) :
    S.card = 1 + (D.outN S v).card + (D.inN S v).card + (D.nonN S v).card := by
  have := D.sum_split hv (fun _ => 1)
  simpa using this

theorem deg_eq_sum (A : Finset V) (x : V) :
    D.deg A x = ∑ y ∈ A, if D.adj x y then 1 else 0 := by
  unfold deg; rw [Finset.card_filter]

theorem deg_split {S : Finset V} {v : V} (hv : v ∈ S) (x : V) :
    D.deg S x = (if D.adj x v then 1 else 0) + D.deg (D.outN S v) x + D.deg (D.inN S v) x
      + D.deg (D.nonN S v) x := by
  simp only [deg_eq_sum]; exact D.sum_split hv _

/-- The degree is out-degree plus in-degree. -/
theorem deg_eq (S : Finset V) (v : V) :
    D.deg S v = (D.outN S v).card + (D.inN S v).card := by
  unfold deg outN inN
  have h : S.filter (fun y => D.adj v y)
      = S.filter (fun y => D.arc v y) ∪ S.filter (fun y => D.arc y v) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    unfold adj; tauto
  rw [h, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]; intro y _ h1 h2; exact D.asymm v y h1 h2

theorem E_comm (A X : Finset V) : D.E A X = D.E X A := by
  unfold E; simp only [deg_eq_sum]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro x _
  exact if_congr D.adj_symm rfl rfl

/-- Paper, equation (4): the degree sum over `C = I(v)`. -/
theorem degsum {S : Finset V} {v : V} (hv : v ∈ S) :
    ∑ c ∈ D.nonN S v, D.deg S c = D.E (D.outN S v) (D.nonN S v)
      + D.E (D.inN S v) (D.nonN S v) + D.E (D.nonN S v) (D.nonN S v) := by
  unfold E
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [D.deg_split hv c]
  have : ¬ D.adj c v := fun h => (mem_nonN.1 hc).2.2 (D.adj_symm.1 h)
  simp [this]

/-- Paper, Lemma 2 (i): `N⁺(v)` is independent. -/
theorem indep_outN (hTT : ¬ D.HasTT) (S : Finset V) (v : V) : D.IsIndep (D.outN S v) := by
  intro x hx y hy hxy
  exact hTT ⟨v, x, y, (mem_outN.1 hx).2, hxy, (mem_outN.1 hy).2⟩

/-- Paper, Lemma 2 (i): `N⁻(v)` is independent. -/
theorem indep_inN (hTT : ¬ D.HasTT) (S : Finset V) (v : V) : D.IsIndep (D.inN S v) := by
  intro x hx y hy hxy
  exact hTT ⟨x, y, v, hxy, (mem_inN.1 hy).2, (mem_inN.1 hx).2⟩

theorem card_outN_lt (hTT : ¬ D.HasTT) {S : Finset V} {n : ℕ} (h : D.NoIndep S n) (v : V) :
    (D.outN S v).card < n := h _ (D.outN_subset S v) (D.indep_outN hTT S v)

theorem card_inN_lt (hTT : ¬ D.HasTT) {S : Finset V} {n : ℕ} (h : D.NoIndep S n) (v : V) :
    (D.inN S v).card < n := h _ (D.inN_subset S v) (D.indep_inN hTT S v)

/-- Paper, Lemma 2 (ii): `D[I(v)]` has no independent set of `n - 1` vertices. -/
theorem noIndep_nonN {S : Finset V} {n : ℕ} {v : V} (hv : v ∈ S) (h : D.NoIndep S (n + 1)) :
    D.NoIndep (D.nonN S v) n := by
  intro T hT hI
  have hvT : v ∉ T := fun hvT => (mem_nonN.1 (hT hvT)).2.1 rfl
  have h1 : D.IsIndep (insert v T) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.1 hx with hx | hx <;> rcases Finset.mem_insert.1 hy with hy | hy
    · rw [hx, hy] at hxy; exact D.arc_irrefl _ hxy
    · rw [hx] at hxy; exact (mem_nonN.1 (hT hy)).2.2 (Or.inl hxy)
    · rw [hy] at hxy; exact (mem_nonN.1 (hT hx)).2.2 (Or.inr hxy)
    · exact hI x hx y hy hxy
  have h2 := h (insert v T) (by
    intro z hz
    rcases Finset.mem_insert.1 hz with hz | hz
    · rw [hz]; exact hv
    · exact (mem_nonN.1 (hT hz)).1) h1
  rw [Finset.card_insert_of_notMem hvT] at h2
  omega

end OGraph

/-- `Bound n N`: in every oriented graph with no transitive triangle, a vertex set with no
independent set of `n` vertices has fewer than `N` vertices. Taking the whole vertex set,
this says `k(n,3) ≤ N`. -/
def Bound (n N : ℕ) : Prop :=
  ∀ (V : Type) (D : OGraph V), ¬ D.HasTT → ∀ S : Finset V, D.NoIndep S n → S.card < N

theorem bound_one : Bound 1 1 := by
  intro V D _ S h
  by_contra hc
  have hne : S.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨x, hx⟩ := hne
  have := h {x} (Finset.singleton_subset_iff.2 hx) (by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]; exact D.arc_irrefl _)
  simp at this

/-- Paper, Remark 13 (Lemma 2.3 of Ihringer, Rajendraprasad and Weinert for `L_3`):
`k(n+1,3) ≤ k(n,3) + 2n + 1`. -/
theorem bound_succ {n N : ℕ} (h : Bound n N) : Bound (n + 1) (N + 2 * n + 1) := by
  intro V D hTT S hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · simp
  · have h1 := D.card_split hv
    have h2 := D.card_outN_lt hTT hS v
    have h3 := D.card_inN_lt hTT hS v
    have h4 := h V D hTT _ (D.noIndep_nonN hv hS)
    omega

/-- `k(2,3) ≤ 4` (paper, Theorem 3). -/
theorem bound_2_4 : Bound 2 4 := bound_succ bound_one

/-- `k(3,3) ≤ 9` (paper, Theorem 3; Bermond). -/
theorem bound_3_9 : Bound 3 9 := bound_succ bound_2_4

/-- To prove `Bound n N` it is enough to exclude vertex sets of exactly `N` vertices. -/
theorem bound_of_exact {n N : ℕ}
    (h : ∀ (V : Type) (D : OGraph V), ¬ D.HasTT → ∀ S : Finset V, D.NoIndep S n →
      S.card = N → False) : Bound n N := by
  intro V D hTT S hS
  by_contra hc
  obtain ⟨S', hS', hc'⟩ := Finset.exists_subset_card_eq (show N ≤ S.card by omega)
  exact h V D hTT S' (D.noIndep_mono hS' hS) hc'

namespace OGraph

variable {V : Type} (D : OGraph V)

theorem card_le_E_add (A X : Finset V) :
    X.card ≤ D.E A X + (X.filter (fun x => D.deg A x = 0)).card := by
  unfold E
  rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum; intro x _; split_ifs <;> omega

/-- The vertices of `X` with no neighbour in the independent set `A` contain no independent
set of `n - |A|` vertices (first paragraph of the proof of Lemma 4 of the paper). -/
theorem noIndep_zero {S A X : Finset V} {n k : ℕ} (hS : D.NoIndep S n) (hA : A ⊆ S)
    (hX : X ⊆ S) (hAI : D.IsIndep A) (hd : Disjoint A X) (hk : A.card + k = n) :
    D.NoIndep (X.filter (fun x => D.deg A x = 0)) k := by
  intro T hT hTI
  have hTX : T ⊆ X := hT.trans (Finset.filter_subset _ _)
  have h1 : D.IsIndep (A ∪ T) := by
    apply D.isIndep_union hAI hTI
    intro a ha b hb hab
    have hb0 := (Finset.mem_filter.1 (hT hb)).2
    unfold deg at hb0
    rw [Finset.card_eq_zero] at hb0
    have : a ∈ A.filter (fun y => D.adj b y) := Finset.mem_filter.2 ⟨ha, D.adj_symm.1 hab⟩
    rw [hb0] at this
    exact absurd this (Finset.notMem_empty a)
  have h2 := hS (A ∪ T) (Finset.union_subset hA (hTX.trans hX)) h1
  rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hTX hd)] at h2
  omega

/-- Paper, Lemma 4 (b). -/
theorem count_b (hTT : ¬ D.HasTT) {S A X : Finset V} {n : ℕ} (hS : D.NoIndep S n)
    (hA : A ⊆ S) (hX : X ⊆ S) (hAI : D.IsIndep A) (hd : Disjoint A X)
    (hk : A.card + 2 = n) : X.card ≤ D.E A X + 3 := by
  have h1 := D.card_le_E_add A X
  have h2 := bound_2_4 V D hTT _ (D.noIndep_zero hS hA hX hAI hd hk)
  omega

/-- Paper, Lemma 4 (c). -/
theorem count_c (hTT : ¬ D.HasTT) {S A X : Finset V} {n : ℕ} (hS : D.NoIndep S n)
    (hA : A ⊆ S) (hX : X ⊆ S) (hAI : D.IsIndep A) (hd : Disjoint A X)
    (hk : A.card + 3 = n) : X.card ≤ D.E A X + 8 := by
  have h1 := D.card_le_E_add A X
  have h2 := bound_3_9 V D hTT _ (D.noIndep_zero hS hA hX hAI hd hk)
  omega

/-- Paper, Lemma 4 (a) (Lemma 3.3 of Ihringer, Rajendraprasad and Weinert):
`e(A,X) ≥ 2(|X| - n + 1)` when `|A| = n - 1`. -/
theorem count_a (hTT : ¬ D.HasTT) {S A X : Finset V} {n : ℕ} (hS : D.NoIndep S n)
    (hA : A ⊆ S) (hX : X ⊆ S) (hAI : D.IsIndep A) (hd : Disjoint A X)
    (hk : A.card + 1 = n) : 2 * X.card ≤ D.E A X + 2 * A.card := by
  have h0 : (X.filter (fun x => D.deg A x = 0)).card = 0 := by
    have := bound_one V D hTT _ (D.noIndep_zero hS hA hX hAI hd hk); omega
  have h1 : (X.filter (fun x => D.deg A x = 1)).card ≤ 2 * A.card := by
    let Sa : V → Finset V := fun a => X.filter (fun x => A.filter (fun y => D.adj x y) = {a})
    have hsub : X.filter (fun x => D.deg A x = 1) ⊆ A.biUnion Sa := by
      intro x hx
      obtain ⟨hxX, hx1⟩ := Finset.mem_filter.1 hx
      unfold deg at hx1
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hx1
      have haA : a ∈ A := by
        have : a ∈ A.filter (fun y => D.adj x y) := by
          rw [ha]; exact Finset.mem_singleton_self a
        exact (Finset.mem_filter.1 this).1
      exact Finset.mem_biUnion.2 ⟨a, haA, Finset.mem_filter.2 ⟨hxX, ha⟩⟩
    have hSa : ∀ a ∈ A, (Sa a).card ≤ 2 := by
      intro a haA
      have key : ∀ x ∈ Sa a, ∀ y ∈ Sa a, x ≠ y → D.adj x y := by
        intro x hx y hy hxy
        by_contra hna
        obtain ⟨hxX, hxa⟩ := Finset.mem_filter.1 hx
        obtain ⟨hyX, hya⟩ := Finset.mem_filter.1 hy
        have hxA : x ∉ A := fun h => (Finset.disjoint_left.1 hd h) hxX
        have hyA : y ∉ A := fun h => (Finset.disjoint_left.1 hd h) hyX
        have hI : D.IsIndep (A.erase a ∪ {x, y}) := by
          apply D.isIndep_union (D.isIndep_mono hAI (Finset.erase_subset _ _))
          · intro p hp q hq hpq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
            rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq] at hpq
            · exact D.arc_irrefl _ hpq
            · exact hna (Or.inl hpq)
            · exact hna (Or.inr hpq)
            · exact D.arc_irrefl _ hpq
          · intro b hb p hp hbp
            obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with hp | hp <;> rw [hp] at hbp
            · have : b ∈ A.filter (fun y => D.adj x y) :=
                Finset.mem_filter.2 ⟨hbA, D.adj_symm.1 hbp⟩
              rw [hxa, Finset.mem_singleton] at this; exact hba this
            · have : b ∈ A.filter (fun w => D.adj y w) :=
                Finset.mem_filter.2 ⟨hbA, D.adj_symm.1 hbp⟩
              rw [hya, Finset.mem_singleton] at this; exact hba this
        have hsubS : A.erase a ∪ {x, y} ⊆ S := by
          apply Finset.union_subset ((Finset.erase_subset _ _).trans hA)
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz | hz <;> rw [hz]
          · exact hX hxX
          · exact hX hyX
        have hc := hS _ hsubS hI
        have hcard : (A.erase a ∪ {x, y}).card = A.card + 1 := by
          rw [Finset.card_union_of_disjoint, Finset.card_erase_of_mem haA, Finset.card_pair hxy]
          · have := Finset.card_pos.2 ⟨a, haA⟩; omega
          · rw [Finset.disjoint_left]; intro z hz hz'
            have hzA := (Finset.mem_erase.1 hz).2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
            rcases hz' with h | h <;> rw [h] at hzA
            · exact hxA hzA
            · exact hyA hzA
        omega
      have hout : ((Sa a).filter (fun x => D.arc a x)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        by_contra hxy
        obtain ⟨hxS, hax⟩ := Finset.mem_filter.1 hx
        obtain ⟨hyS, hay⟩ := Finset.mem_filter.1 hy
        rcases key x hxS y hyS hxy with h | h
        · exact hTT ⟨a, x, y, hax, h, hay⟩
        · exact hTT ⟨a, y, x, hay, h, hax⟩
      have hin : ((Sa a).filter (fun x => ¬ D.arc a x)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        by_contra hxy
        obtain ⟨hxS, hax⟩ := Finset.mem_filter.1 hx
        obtain ⟨hyS, hay⟩ := Finset.mem_filter.1 hy
        have toA : ∀ z ∈ Sa a, ¬ D.arc a z → D.arc z a := by
          intro z hz hnz
          have : a ∈ A.filter (fun w => D.adj z w) := by
            rw [(Finset.mem_filter.1 hz).2]; exact Finset.mem_singleton_self a
          rcases (Finset.mem_filter.1 this).2 with h | h
          · exact h
          · exact absurd h hnz
        have hxa := toA x hxS hax
        have hya := toA y hyS hay
        rcases key x hxS y hyS hxy with h | h
        · exact hTT ⟨x, y, a, h, hya, hxa⟩
        · exact hTT ⟨y, x, a, h, hxa, hya⟩
      have := Finset.card_filter_add_card_filter_not (s := Sa a) (fun x => D.arc a x)
      omega
    calc (X.filter (fun x => D.deg A x = 1)).card
        ≤ (A.biUnion Sa).card := Finset.card_le_card hsub
      _ ≤ ∑ a ∈ A, (Sa a).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ A, 2 := Finset.sum_le_sum hSa
      _ = 2 * A.card := by simp [mul_comm]
  have h2 : 2 * X.card ≤ D.E A X + (X.filter (fun x => D.deg A x = 1)).card
      + 2 * (X.filter (fun x => D.deg A x = 0)).card := by
    have hX2 : 2 * X.card = ∑ x ∈ X, 2 := by simp [mul_comm]
    unfold E
    rw [hX2, Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro x _; split_ifs <;> omega
  omega

end OGraph

end Erdos112
