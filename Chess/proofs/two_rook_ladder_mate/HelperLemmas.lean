import ChessRules
import FunctionDefinition
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

-- moving rook into a square one rank up in the same file is a ValidRookMove
lemma RookUp_IsValid {n : Nat} (b : Board n) (src tgt : Pos n)
    (same_col : src.file = tgt.file)
    (tgt_close : src.rank.val + 1 = tgt.rank.val) :
    ValidRookMove b src tgt := by
  refine ⟨?_, .inr ⟨same_col, ?_⟩⟩
  · intro h
    have := congrArg (·.rank.val) h
    simp at this
    omega
  · intro p hpfile hbet
    -- between rank src and rank tgt with diff 1, no integer strictly between
    unfold Between at hbet
    omega

-- king analogue of RookUp_IsValid: a king step up by one rank
-- in the same file is a ValidKingMove
lemma KingUp_IsValid {n : Nat} (src tgt : Pos n)
    (same_col : src.file = tgt.file)
    (tgt_close : src.rank.val + 1 = tgt.rank.val) :
    ValidKingMove src tgt := by
  have hf : src.file.val = tgt.file.val := congrArg Fin.val same_col
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg (·.rank.val) h
    simp at this
    omega
  · unfold WithinOne; omega
  · unfold WithinOne; omega

-- if we start from IsLegalSetup, and make any move into an empty square,
-- then there is a unique black king and a unique white king
lemma NoCaputureMove_PreservesKings {n : Nat} (b : Board n)
    (src tgt : Pos n) (legal_start : IsLegalSetup b)
    (tgt_empty : b tgt = none) :
  let b_new := applyMove b src tgt
  (∃! wp : Pos n, b_new wp = some ⟨.White, .King⟩) ∧
  (∃! bp : Pos n, b_new bp = some ⟨.Black, .King⟩) := by
  show (∃! wp : Pos n, (applyMove b src tgt) wp = some ⟨.White, .King⟩) ∧
       (∃! bp : Pos n, (applyMove b src tgt) bp = some ⟨.Black, .King⟩)
  obtain ⟨wkU, bkU, _⟩ := legal_start
  have applyMove_eq : ∀ p,
      (applyMove b src tgt) p =
        if p = tgt then b src else if p = src then none else b p := by
    intro p
    show (applyMove b src tgt).pieces p = _
    unfold applyMove
    by_cases h1 : p = tgt
    · simp [h1]
    · by_cases h2 : p = src
      · simp [h2]
      · simp [h1, h2]
  have preserve : ∀ (P : Piece) (_ : ∃! u, b u = some P),
      ∃! u, (applyMove b src tgt) u = some P := by
    intro P ⟨u, hu, hu_uniq⟩
    have hu_ne_tgt : u ≠ tgt := by
      intro h
      rw [h, tgt_empty] at hu
      cases hu
    by_cases hsrc_eq : src = u
    · refine ⟨tgt, ?_, ?_⟩
      · show (applyMove b src tgt) tgt = _
        rw [applyMove_eq, if_pos rfl, hsrc_eq]; exact hu
      · intro y hy
        rw [applyMove_eq] at hy
        by_cases h1 : y = tgt
        · exact h1
        · rw [if_neg h1] at hy
          by_cases h2 : y = src
          · rw [if_pos h2] at hy
            cases hy
          · rw [if_neg h2] at hy
            have hyu := hu_uniq y hy
            exact absurd (hyu.trans hsrc_eq.symm) h2
    · have hbsrc_ne : b src ≠ some P := by
        intro hbsrc
        exact hsrc_eq (hu_uniq src hbsrc).symm.symm
      have hu_ne_src : u ≠ src := fun h => hsrc_eq h.symm
      refine ⟨u, ?_, ?_⟩
      · show (applyMove b src tgt) u = _
        rw [applyMove_eq, if_neg hu_ne_tgt, if_neg hu_ne_src]; exact hu
      · intro y hy
        rw [applyMove_eq] at hy
        by_cases h1 : y = tgt
        · rw [if_pos h1] at hy
          exact absurd hy hbsrc_ne
        · rw [if_neg h1] at hy
          by_cases h2 : y = src
          · rw [if_pos h2] at hy
            cases hy
          · rw [if_neg h2] at hy
            exact hu_uniq y hy
  exact ⟨preserve _ wkU, preserve _ bkU⟩

-- if white king is at least two files away from black king,
-- and black king is the only black piece,
-- then white king is not in check
lemma OpponentOnlyKingFarAway_NoCheck {n : Nat} (b : Board n)
    (only_black_king : ∀ p k, b p = some ⟨.Black, k⟩ → k = .King)
    (kings_apart : ∀ pw pb : Pos n,
      (b pw = some ⟨.White, .King⟩ ∧ b pb = some ⟨.Black, .King⟩) →
      pw.file.val + 2 <= pb.file.val) :
    ¬ IsCheck b .White := by
  rintro ⟨wkPos, hwk, attacker, hatt⟩
  rcases hatt with ⟨hr, _⟩ | ⟨hbk, hkmove⟩
  · exact PieceType.noConfusion (only_black_king attacker .Rook hr)
  · obtain ⟨_, _, hwo⟩ := hkmove
    have apart := kings_apart wkPos attacker ⟨hwk, hbk⟩
    unfold WithinOne at hwo
    omega

-- an empty target square cannot be friendly-occupied, regardless of
-- whose turn it is.
lemma EmptySquare_NotFriendly {n : Nat} (b : Board n) (dst : Pos n)
    (dst_empty : b dst = none) :
    ¬ IsFriendlyOccupied b dst := by
  rintro ⟨_, h⟩
  rw [dst_empty] at h
  cases h

-- A non-capture move preserves any piece sitting on a square other
-- than `src`. `tgt`-emptiness rules out `p = tgt` (since `b p = some _`
-- can't equal `b tgt = none`), and `src ≠ p` rules out the cleared
-- square; everywhere else `applyMove` returns `b p` unchanged.
lemma NoCaptureMove_PreservesPiece {n : Nat} (b : Board n) (src tgt p : Pos n)
    (pc : Piece) (h_p_at : b p = some pc) (h_src_ne_p : src ≠ p)
    (tgt_empty : b tgt = none) :
    (applyMove b src tgt) p = some pc := by
  show (applyMove b src tgt).pieces p = some pc
  unfold applyMove
  have h_p_ne_tgt : p ≠ tgt := by
    intro heq; rw [heq, tgt_empty] at h_p_at; cases h_p_at
  have h_p_ne_src : p ≠ src := fun h => h_src_ne_p h.symm
  simp [h_p_ne_tgt, h_p_ne_src]
  exact h_p_at

-- any move on a board where every black piece is a king preserves
-- that property: the only piece relocated lands at `tgt`, and if it
-- was black it was a king by hypothesis.
lemma applyMove_PreservesOnlyBlackKing {n : Nat} (b : Board n) (src tgt : Pos n)
    (only_bk : ∀ p k, b p = some ⟨.Black, k⟩ → k = .King) :
    ∀ p k, (applyMove b src tgt) p = some ⟨.Black, k⟩ → k = .King := by
  intro p k hp
  have hp' : (applyMove b src tgt).pieces p = some ⟨.Black, k⟩ := hp
  unfold applyMove at hp'
  by_cases h1 : p = tgt
  · simp [h1] at hp'
    exact only_bk src k hp'
  · by_cases h2 : p = src
    · simp [h2] at hp'
      exact only_bk src k hp'.2
    · simp [h1, h2] at hp'
      exact only_bk p k hp'


-- ============================================================
-- COLOR-PIECE COUNTING (helpers for `LadderShape` invariant Q)
-- ============================================================
-- The conjunct
--   Q : ∀ p, (∃ k, board p = some ⟨.White, k⟩) → p = K ∨ p = Rb ∨ p = Ra
-- in `LadderShape` is preserved across one White ply + one legal Black
-- reply. Rather than a direct case-analysis tying every sub-fact to the
-- ladder's three named squares, we factor through a counting argument
-- that splits cleanly into reusable, board-level pieces. The lemmas
-- below are color-agnostic (parameterised by `(c : Color)`) so the
-- same machinery is available for future setups that track black-
-- piece confinement instead.
--
--   (a) Any non-capturing move preserves the *number* of squares
--       occupied by pieces of color `c`. This is a generic fact
--       about boards, independent of any specific named squares.
--       It splits into two sub-cases:
--         · Friendly ply (a `c`-piece relocates onto an empty square):
--           one element leaves `colorSquares`, one element enters,
--           card unchanged.
--         · Opponent ply (a `c.opponent`-piece relocates onto an
--           empty square): `colorSquares b c` is *literally identical*
--           before and after — no `c`-piece is touched at all.
--
--   (b) The three named squares each carry a `c`-piece in the
--       post-move board. The per-phase `LadderStep_PiecesAt_*`
--       lemmas (plus `whitePiecePreserved` for the black ply)
--       already give us this for the white case.
--
--   (c) The three named squares are pairwise distinct. Purely
--       combinatorial; for the ladder, this drops out of the
--       rank/file definitions in `FunctionDefinition.lean`.
--
-- Putting them together: from Q on the original board we get
-- `(colorSquares b c).card ≤ 3`; (a) propagates the bound to the
-- new board; (b)+(c) provide a 3-element subset of
-- `colorSquares b' c`; `Finset.eq_of_subset_of_card_le` then
-- collapses inequality to equality, which is exactly Q for the
-- new board.
--
-- Why `≤ 3` and not `= 3`?
--   The natural fact derived from Q is "subset of a 3-element set",
--   i.e., `card ≤ 3` — no distinctness needed at this stage. It is
--   also exactly the input shape `Finset.eq_of_subset_of_card_le`
--   wants. Using `= 3` would force us to prove the lower bound (≥ 3,
--   needing the three positions distinct) twice: once to seed the
--   invariant and once at every preservation step. With `≤ 3` we
--   carry one half of the count and only invoke distinctness at the
--   final collapse step (`Q_of_subset_card_le` below).

instance Pos.fintype {n : Nat} : Fintype (Pos n) :=
  Fintype.ofEquiv (Fin n × Fin n)
    { toFun := fun ⟨r, f⟩ => ⟨r, f⟩
      invFun := fun p => (p.rank, p.file)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The set of squares carrying a piece of color `c`. -/
def colorSquares {n : Nat} (b : Board n) (c : Color) : Finset (Pos n) :=
  Finset.univ.filter (fun p => ∃ k, b p = some ⟨c, k⟩)

-- Step A: from "c-pieces are confined to {p1, p2, p3}" we get a
-- card bound. No distinctness needed: even if some of the three
-- coincide, the card of the image is ≤ 3.
lemma colorSquares_card_le_three_of_Q {n : Nat} (b : Board n) (c : Color)
    {p1 p2 p3 : Pos n}
    (hQ : ∀ p, (∃ k, b p = some ⟨c, k⟩) →
          p = p1 ∨ p = p2 ∨ p = p3) :
    (colorSquares b c).card ≤ 3 := by
  have h_sub : colorSquares b c ⊆ ({p1, p2, p3} : Finset (Pos n)) := by
    intro p hp
    simp only [colorSquares, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have := hQ p hp
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact this
  calc (colorSquares b c).card
      ≤ ({p1, p2, p3} : Finset (Pos n)).card := Finset.card_le_card h_sub
    _ ≤ 3 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.add_le_add_right ?_ 1
        refine (Finset.card_insert_le _ _).trans ?_
        simp [Finset.card_singleton]

-- Step B (friendly ply): a non-capturing move that relocates a piece
-- of color `c` to an empty square preserves the count of `c`-squares.
-- Generic — does not mention any specific named squares. The premises
-- are what the ladder gives us for white plies: src has a `c`-piece
-- (from the invariant), dst is empty (from `LadderMove_IntoEmptySquare`).
lemma colorSquares_card_eq_friendlyNonCapture {n : Nat} (b : Board n) (c : Color)
    (src dst : Pos n)
    (h_src : ∃ k, b src = some ⟨c, k⟩)
    (h_dst_empty : b dst = none) :
    (colorSquares (applyMove b src dst) c).card = (colorSquares b c).card := by
  obtain ⟨k_src, h_src_at⟩ := h_src
  have h_src_in : src ∈ colorSquares b c := by
    simp only [colorSquares, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k_src, h_src_at⟩
  have h_dst_notin : dst ∉ colorSquares b c := by
    simp only [colorSquares, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨k, hk⟩
    rw [h_dst_empty] at hk; cases hk
  have apply_eq : ∀ p, (applyMove b src dst).pieces p =
      if p = dst then b src else if p = src then none else b p := by
    intro p
    unfold applyMove
    by_cases h1 : p = dst
    · simp [h1]
    · by_cases h2 : p = src
      · simp [h2]
      · simp [h1, h2]
  -- The new white-square set is the old one with src removed and dst added.
  have h_set_eq : colorSquares (applyMove b src dst) c =
      insert dst ((colorSquares b c).erase src) := by
    ext p
    simp only [colorSquares, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_insert, Finset.mem_erase]
    show (∃ k, (applyMove b src dst).pieces p = some ⟨c, k⟩) ↔
         p = dst ∨ p ≠ src ∧ ∃ k, b p = some ⟨c, k⟩
    rw [apply_eq]
    by_cases h1 : p = dst
    · subst h1
      rw [if_pos rfl]
      refine ⟨fun _ => Or.inl rfl, fun _ => ⟨k_src, h_src_at⟩⟩
    · rw [if_neg h1]
      by_cases h2 : p = src
      · subst h2
        rw [if_pos rfl]
        refine ⟨fun ⟨_, hk⟩ => ?_, ?_⟩
        · cases hk
        · rintro (h | ⟨h, _⟩)
          · exact (h1 h).elim
          · exact (h rfl).elim
      · rw [if_neg h2]
        refine ⟨fun h => Or.inr ⟨h2, h⟩, ?_⟩
        rintro (h | ⟨_, h⟩)
        · exact (h1 h).elim
        · exact h
  rw [h_set_eq]
  have h_dst_not_in_erase : dst ∉ (colorSquares b c).erase src := by
    rw [Finset.mem_erase]; rintro ⟨_, h⟩; exact h_dst_notin h
  rw [Finset.card_insert_of_notMem h_dst_not_in_erase,
      Finset.card_erase_of_mem h_src_in]
  have h_pos : (colorSquares b c).card ≥ 1 :=
    Finset.card_pos.mpr ⟨src, h_src_in⟩
  omega

-- Step B (opponent ply): a non-capturing move whose source carries a
-- `c.opponent`-piece leaves `colorSquares _ c` literally unchanged.
-- Strictly stronger than the friendly-ply lemma (no card needed)
-- because pieces of the opposite color cannot enter or leave
-- `colorSquares _ c`. The `h_dst_empty` premise is the "non-capturing"
-- assumption (currently `sorry`'d in `LadderShape.preservation` as
-- `bdst_empty`).
lemma colorSquares_eq_opponentNonCapture {n : Nat} (b : Board n) (c : Color)
    (src dst : Pos n)
    (h_src : ∃ k, b src = some ⟨c.opponent, k⟩)
    (h_dst_empty : b dst = none) :
    colorSquares (applyMove b src dst) c = colorSquares b c := by
  obtain ⟨k_opp, h_src_at⟩ := h_src
  have h_color_ne : c.opponent ≠ c := by cases c <;> decide
  have h_src_not_c : ∀ k, b src ≠ some ⟨c, k⟩ := fun k h => by
    rw [h_src_at] at h
    exact h_color_ne (congrArg Piece.color (Option.some.inj h))
  have h_dst_not_c : ∀ k, b dst ≠ some ⟨c, k⟩ := fun k h => by
    rw [h_dst_empty] at h; cases h
  have apply_eq : ∀ p, (applyMove b src dst).pieces p =
      if p = dst then b src else if p = src then none else b p := by
    intro p
    unfold applyMove
    by_cases h1 : p = dst
    · simp [h1]
    · by_cases h2 : p = src
      · simp [h2]
      · simp [h1, h2]
  ext p
  simp only [colorSquares, Finset.mem_filter, Finset.mem_univ, true_and]
  show (∃ k, (applyMove b src dst).pieces p = some ⟨c, k⟩) ↔
       (∃ k, b p = some ⟨c, k⟩)
  rw [apply_eq p]
  by_cases h1 : p = dst
  · subst h1
    rw [if_pos rfl]
    exact ⟨fun ⟨k, hk⟩ => (h_src_not_c k hk).elim,
           fun ⟨k, hk⟩ => (h_dst_not_c k hk).elim⟩
  · rw [if_neg h1]
    by_cases h2 : p = src
    · subst h2
      rw [if_pos rfl]
      refine ⟨fun ⟨_, hk⟩ => ?_, fun ⟨k, hk⟩ => (h_src_not_c k hk).elim⟩
      cases hk
    · rw [if_neg h2]

-- Step C: closing lemma. Given three pairwise distinct positions
-- carrying `c`-pieces, plus the `≤ 3` count bound (from steps A/B),
-- we recover Q via `Finset.eq_of_subset_of_card_le`. The piece type
-- at each position is left existential — only color matters here.
lemma Q_of_subset_card_le {n : Nat} (b : Board n) (c : Color)
    {p1 p2 p3 : Pos n}
    (h1 : ∃ k, b p1 = some ⟨c, k⟩)
    (h2 : ∃ k, b p2 = some ⟨c, k⟩)
    (h3 : ∃ k, b p3 = some ⟨c, k⟩)
    (h_12 : p1 ≠ p2) (h_13 : p1 ≠ p3) (h_23 : p2 ≠ p3)
    (h_card : (colorSquares b c).card ≤ 3) :
    ∀ p, (∃ k, b p = some ⟨c, k⟩) →
         p = p1 ∨ p = p2 ∨ p = p3 := by
  have h_sub : ({p1, p2, p3} : Finset (Pos n)) ⊆ colorSquares b c := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    simp only [colorSquares, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hp with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have h_card_three : ({p1, p2, p3} : Finset (Pos n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
    · simp [h_23]
    · simp [Finset.mem_insert, Finset.mem_singleton, h_12, h_13]
  have h_eq : ({p1, p2, p3} : Finset (Pos n)) = colorSquares b c :=
    Finset.eq_of_subset_of_card_le h_sub (h_card_three ▸ h_card)
  intro p hp
  have hp_in : p ∈ colorSquares b c := by
    simp only [colorSquares, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp
  rw [← h_eq] at hp_in
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp_in
  exact hp_in

