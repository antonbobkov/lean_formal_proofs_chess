import ChessRules
import FunctionDefinition

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

