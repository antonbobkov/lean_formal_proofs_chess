import ChessRules
import FunctionDefinition

-- if a square above rook is empty, then moving into that
-- square is ValidRookMove
lemma RookUpEmpty_IsValid {n : Nat} (b : Board n) (src tgt : Pos n)
    (_tgt_empty : b tgt = none) (same_col : src.file = tgt.file)
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

-- king analogue of RookUpEmpty_IsValid: a king step up by one rank
-- in the same file is a ValidKingMove (no emptiness needed — kings
-- don't slide).
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
  (∃! bp : Pos n, b_new bp = some ⟨.Black, .King⟩) := by sorry

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
    ∀ p k, b' p = some ⟨.Black, k⟩ → k = .King := by sorry
