import Erdos112.Defs

/-!
# The lower bound: the oriented graph `G_29` (paper, Section 3 and Appendix A)

`rows29` is Table 1 of the paper: row `v` (counting from 0) lists the out-neighbours of `v`.
It was generated from the deposit file `witness_n29_m6_anneal.txt`.

Everything in this file is checked by the Lean kernel (`decide +kernel` evaluates the
checks inside the kernel; no `native_decide`, no compiler trust).
-/

namespace Erdos112

/-- Table 1 of the paper: the out-neighbours of the vertices `0, ..., 28` of `G_29`. -/
def rows29 : List (List Nat) :=
  [[6, 15, 22, 23, 28],
   [5, 13, 22, 24],
   [0, 8, 17, 19, 20],
   [0, 5, 9, 18, 20],
   [2, 10, 11, 13, 18],
   [6, 10, 14, 16],
   [2, 3, 7, 21],
   [0, 1, 9, 12, 25],
   [1, 9, 12, 23, 28],
   [6, 10, 13, 22, 26],
   [3, 7, 8, 17, 19],
   [12, 17, 19, 20, 28],
   [4, 6, 15, 22, 26],
   [7, 8, 14, 19, 27],
   [1, 3, 17, 25],
   [13, 16, 18, 21, 24],
   [2, 3, 11, 25, 27],
   [4, 5, 9, 23, 24],
   [12, 19, 25, 27],
   [1, 4, 9, 15, 23],
   [4, 6, 16, 23, 24],
   [0, 8, 11, 25, 27],
   [7, 14, 16, 18, 21],
   [2, 10, 13, 21, 26],
   [2, 10, 11, 14, 27],
   [5, 15, 20, 22, 28],
   [7, 8, 11, 14, 18],
   [1, 15, 17, 20, 28],
   [4, 16, 21, 24, 26]]

/-- `arcB i j = true` when `j` is listed in row `i`, that is, `i → j` in `G_29`. -/
def arcB (i j : Nat) : Bool := (rows29.getD i []).contains j

/-- `nadjB i j = true` when `i` and `j` are not adjacent. -/
def nadjB (i j : Nat) : Bool := !(arcB i j) && !(arcB j i)

/-- Step 1 of the proof of Theorem 5: the table defines an oriented graph. -/
theorem G29_asymm : ∀ x, x < 29 → ∀ y, y < 29 → arcB x y = true → arcB y x = false := by
  decide +kernel

/-- The oriented graph `G_29` on the vertex set `{0, ..., 28}`. -/
def G29 : OGraph (Fin 29) where
  arc i j := arcB i.val j.val = true
  asymm := by
    intro x y h
    have := G29_asymm x.val x.isLt y.val y.isLt h
    simp [this]

/-- Step 2 of the proof of Theorem 5: for all arcs `x → y` and `y → z`, there is no arc
`x → z`. -/
theorem G29_tt_check : ∀ x, x < 29 → ∀ y, y < 29 → arcB x y = true →
    ∀ z, z < 29 → arcB y z = true → arcB x z = false := by
  decide +kernel

theorem G29_noTT : ¬ G29.HasTT := by
  rintro ⟨x, y, z, h1, h2, h3⟩
  have := G29_tt_check x.val x.isLt y.val y.isLt h1 z.val z.isLt h2
  have h3' : arcB x.val z.val = true := h3
  rw [this] at h3'
  exact Bool.false_ne_true h3'

/-- `allLt n p` is `true` when `p k` is `true` for every `k < n`. -/
def allLt (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p

theorem allLt_spec {n : Nat} {p : Nat → Bool} (h : allLt n p = true) :
    ∀ k, k < n → p k = true := by
  intro k hk
  unfold allLt at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range.2 hk)

theorem or_step {x y : Bool} (h : (!x || y) = true) (hx : x = true) : y = true := by
  subst hx; simpa using h

theorem not_step {x : Bool} (h : (!(true && x)) = true) : x = false := by
  cases x <;> simp_all

/-- Step 3 of the proof of Theorem 5 as one Boolean computation over increasing tuples
`a < b < c < d < e < f`: no such tuple is pairwise non-adjacent. The nested form stops as
soon as a prefix of the tuple contains an adjacent pair, so it visits every independent set
of at most 5 vertices once (the method of `check_witness.py`). -/
def check6 : Bool :=
  allLt 29 fun a => allLt 29 fun b => !(decide (a < b) && nadjB a b) ||
  allLt 29 fun c => !(decide (b < c) && (nadjB a c && nadjB b c)) ||
  allLt 29 fun d => !(decide (c < d) && (nadjB a d && nadjB b d && nadjB c d)) ||
  allLt 29 fun e => !(decide (d < e) && (nadjB a e && nadjB b e && nadjB c e && nadjB d e)) ||
  allLt 29 fun f => !(decide (e < f) &&
    (nadjB a f && nadjB b f && nadjB c f && nadjB d f && nadjB e f))

/-- The computation, evaluated by the Lean kernel. -/
theorem check6_true : check6 = true := by decide +kernel

theorem G29_sorted_check :
    ∀ a, a < 29 → ∀ b, b < 29 → a < b → nadjB a b = true →
    ∀ c, c < 29 → b < c → (nadjB a c && nadjB b c) = true →
    ∀ d, d < 29 → c < d → (nadjB a d && nadjB b d && nadjB c d) = true →
    ∀ e, e < 29 → d < e → (nadjB a e && nadjB b e && nadjB c e && nadjB d e) = true →
    ∀ f, f < 29 → e < f →
      (nadjB a f && nadjB b f && nadjB c f && nadjB d f && nadjB e f) = false := by
  intro a ha b hb hab n1 c hc hbc n2 d hd hcd n3 e he hde n4 f hf hef
  have h := check6_true
  unfold check6 at h
  have h1 := allLt_spec (allLt_spec h a ha) b hb
  have h2 := allLt_spec (or_step h1 (by rw [decide_eq_true hab, n1]; rfl)) c hc
  have h3 := allLt_spec (or_step h2 (by rw [decide_eq_true hbc, n2]; rfl)) d hd
  have h4 := allLt_spec (or_step h3 (by rw [decide_eq_true hcd, n3]; rfl)) e he
  have h5 := allLt_spec (or_step h4 (by rw [decide_eq_true hde, n4]; rfl)) f hf
  rw [decide_eq_true hef] at h5
  exact not_step h5

/-- `G_29` has no independent set of 6 vertices. -/
theorem G29_no_indep6 : ∀ T : Finset (Fin 29), G29.IsIndep T → T.card ≠ 6 := by
  intro T hT h6
  have hm : ∀ i, T.orderEmbOfFin h6 i ∈ T := fun i => Finset.orderEmbOfFin_mem T h6 i
  have hlt : ∀ i j : Fin 6, i < j → T.orderEmbOfFin h6 i < T.orderEmbOfFin h6 j :=
    fun i j h => (T.orderEmbOfFin h6).strictMono h
  have hn : ∀ i j : Fin 6,
      nadjB (T.orderEmbOfFin h6 i).val (T.orderEmbOfFin h6 j).val = true := by
    intro i j
    have h1 : arcB (T.orderEmbOfFin h6 i).val (T.orderEmbOfFin h6 j).val = false := by
      have := hT _ (hm i) _ (hm j)
      simpa [G29] using this
    have h2 : arcB (T.orderEmbOfFin h6 j).val (T.orderEmbOfFin h6 i).val = false := by
      have := hT _ (hm j) _ (hm i)
      simpa [G29] using this
    simp [nadjB, h1, h2]
  have key := G29_sorted_check
    _ (T.orderEmbOfFin h6 0).isLt
    _ (T.orderEmbOfFin h6 1).isLt (hlt 0 1 (by decide)) (hn 0 1)
    _ (T.orderEmbOfFin h6 2).isLt (hlt 1 2 (by decide)) (by simp [hn])
    _ (T.orderEmbOfFin h6 3).isLt (hlt 2 3 (by decide)) (by simp [hn])
    _ (T.orderEmbOfFin h6 4).isLt (hlt 3 4 (by decide)) (by simp [hn])
    _ (T.orderEmbOfFin h6 5).isLt (hlt 4 5 (by decide))
  simp [hn] at key

/-- **Theorem 5 of the paper**: `G_29` has no transitive triangle and no independent set of
6 vertices. -/
theorem G29_free : G29.Free 6 := ⟨G29_noTT, G29_no_indep6⟩

/-- The 140 arcs of `G_29` (a check of the table, not used elsewhere). -/
theorem G29_arc_count : (rows29.map List.length).sum = 140 ∧ rows29.length = 29 := by
  decide +kernel

end Erdos112
