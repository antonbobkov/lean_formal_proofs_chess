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

-- after applying nextWhiteMove, every black-occupied square is still a
-- black king. White moves cannot create new black pieces; they only
-- relocate white pieces and possibly overwrite the (empty) target.
lemma LadderMove_PreservesOnlyBlackKing {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (ladder_shape : LadderShape board rank φ) :
    let move := nextWhiteMove ladder_shape
    let b'   := applyMove board move.1 move.2
    ∀ p k, b' p = some ⟨.Black, k⟩ → k = .King := by
  show ∀ p k, (applyMove board (nextWhiteMove ladder_shape).1
                (nextWhiteMove ladder_shape).2) p = some ⟨.Black, k⟩ → k = .King
  intro p k hp
  have hbnd : rank.val + 2 < n := ladder_shape.hRfits
  have ls := ladder_shape
  unfold LadderShape at ls
  rw [dif_pos hbnd] at ls
  obtain ⟨_, hK_at, hRb_at, hRa_at, _, _, only_bk, _⟩ := ls
  have h_src_white : ∃ wk,
      board (nextWhiteMove ladder_shape).1 = some ⟨.White, wk⟩ := by
    cases φ
    · exact ⟨.Rook, hRb_at⟩
    · exact ⟨.Rook, hRa_at⟩
    · exact ⟨.King, hK_at⟩
  have hp_eq : (applyMove board (nextWhiteMove ladder_shape).1
                (nextWhiteMove ladder_shape).2).pieces p
             = if p = (nextWhiteMove ladder_shape).2 then
                  board (nextWhiteMove ladder_shape).1
               else if p = (nextWhiteMove ladder_shape).1 then
                  none
               else board p := by
    unfold applyMove
    by_cases h1 : p = (nextWhiteMove ladder_shape).2
    · simp [h1]
    · by_cases h2 : p = (nextWhiteMove ladder_shape).1
      · simp [h2]
      · simp [h1, h2]
  have hp' : (applyMove board (nextWhiteMove ladder_shape).1
              (nextWhiteMove ladder_shape).2).pieces p = some ⟨.Black, k⟩ := hp
  rw [hp_eq] at hp'
  by_cases h1 : p = (nextWhiteMove ladder_shape).2
  · rw [if_pos h1] at hp'
    obtain ⟨_, hk⟩ := h_src_white
    rw [hk] at hp'
    simp at hp'
  · rw [if_neg h1] at hp'
    by_cases h2 : p = (nextWhiteMove ladder_shape).1
    · rw [if_pos h2] at hp'; simp at hp'
    · rw [if_neg h2] at hp'
      exact only_bk p k hp'
