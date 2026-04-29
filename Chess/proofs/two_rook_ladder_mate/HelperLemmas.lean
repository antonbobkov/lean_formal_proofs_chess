import ChessRules
import FunctionDefinition

-- if a square above rook is empty, then moving into that
-- square is ValidRookMove
lemma RookUpEmpty_IsValid {n : Nat} (b : Board n) (src tgt : Pos n)
    (tgt_empty : b tgt = none) (tgt_close : src.1.val + 1 = tgt.1.val) :
    ValidRookMove b src tgt := by sorry

-- king analogue of RookUpEmpty_IsValid: a king step up by one rank
-- in the same file is a ValidKingMove (no emptiness needed — kings
-- don't slide).
lemma KingUp_IsValid {n : Nat} (src tgt : Pos n)
    (same_col : src.2 = tgt.2)
    (tgt_close : src.1.val + 1 = tgt.1.val) :
    ValidKingMove src tgt := by sorry

-- if we start from IsLegalSetup, and make any move into an empty square,
-- then there is a unique black king and a unique white king
lemma NoCaputureMove_PreservesKings {n : Nat} (b : Board n)
    (src tgt : Pos n) (legal_start : IsLegalSetup b)
    (tgt_empty : b tgt = none) :
  let b_new := applyMove b src tgt
  (∃! wp : Pos n, b_new wp = some ⟨.White, .King⟩) ∧
  (∃! bp : Pos n, b_new bp = some ⟨.Black, .King⟩) := by sorry

-- if white king is at least two columns away from black king,
-- and black king is the only black piece,
-- then white king is not in check
lemma OpponentOnlyKing_NoCheck {n : Nat} (b : Board n)
    (only_black_king : ∀ p k, b p = some ⟨.Black, k⟩ → k = .King)
    (kings_close : ∀ pw pb : Pos n,
      (b pw = some ⟨.White, .King⟩ ∧ b pb = some ⟨.Black, .King⟩) →
      pw.1.val + 2 <= pb.1.val) :
    ¬ IsCheck b .White := by sorry

lemma LadderShape_KingsRowsApart {n : Nat} {board : Board n} {rank : Fin n}
  {φ : LadderPhase} (ladder_shape : LadderShape board rank φ) :
     (∀ bp, board bp = some ⟨.Black, .King⟩ → bp.2.val >= 2) := by sorry

lemma LadderMove_IntoEmptySquare {n : Nat} {board : Board n} {rank : Fin n}
  {φ : LadderPhase} (ladder_shape : LadderShape board rank φ) :
    let dst := (nextWhiteMove ladder_shape).2
    board dst = none := by sorry

-- an empty target square cannot be friendly-occupied, regardless of
-- whose turn it is.
lemma EmptySquare_NotFriendly {n : Nat} (b : Board n) (dst : Pos n)
    (dst_empty : b dst = none) :
    ¬ IsFriendlyOccupied b dst := by sorry

-- after applying nextWhiteMove, every black-occupied square is still a
-- black king. White moves cannot create new black pieces; they only
-- relocate white pieces and possibly overwrite the (empty) target.
lemma LadderMove_PreservesOnlyBlackKing {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (ladder_shape : LadderShape board rank φ) :
    let move := nextWhiteMove ladder_shape
    let b'   := applyMove board move.1 move.2
    ∀ p k, b' p = some ⟨.Black, k⟩ → k = .King := by sorry

-- after applying nextWhiteMove, every (white-king, black-king) pair is
-- separated by at least two ranks. Bundles the per-phase arithmetic so
-- the main legality proof can be phase-agnostic.
lemma LadderMove_KingsRowsApart {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (ladder_shape : LadderShape board rank φ) :
    let move := nextWhiteMove ladder_shape
    let b'   := applyMove board move.1 move.2
    ∀ pw pb : Pos n,
      (b' pw = some ⟨.White, .King⟩ ∧ b' pb = some ⟨.Black, .King⟩) →
      pw.1.val + 2 ≤ pb.1.val := by sorry
