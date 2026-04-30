import FunctionDefinition
import HelperLemmas

-- ============================================================
-- LOCAL HELPER LEMMAS
-- ============================================================
-- These bundle the phase-uniform tail of the legality proof so the
-- main theorem only has to handle the phase-specific bits (which
-- piece is at src and which validity helper to invoke).

-- Extracts the conjunction inside `LadderShape` (which is wrapped in
-- a `dite` on the `space_left` bound).
lemma LadderShape.unfold {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    let h := lsh.hRfits
    board.turn = .White ∧
    board (kingPos rank h) = some ⟨.White, .King⟩ ∧
    board (rookBPos rank φ h) = some ⟨.White, .Rook⟩ ∧
    board (rookAPos rank φ h) = some ⟨.White, .Rook⟩ ∧
    (∀ p, (board p = some ⟨.White, .King⟩ ∨
           board p = some ⟨.White, .Rook⟩) →
          p = kingPos rank h ∨
          p = rookBPos rank φ h ∨
          p = rookAPos rank φ h) ∧
    (∀ bp, board bp = some ⟨.Black, .King⟩ →
           (rookAPos rank φ h).rank < bp.rank ∧ 2 ≤ bp.file.val) ∧
    (∀ p k, board p = some ⟨.Black, k⟩ → k = .King) ∧
    IsLegalSetup board := by
  have hbnd := lsh.hRfits
  have h := lsh
  unfold LadderShape at h
  rw [dif_pos hbnd] at h
  exact h

lemma LadderShape_KingsApart {n : Nat} {board : Board n} {rank : Fin n}
  {φ : LadderPhase} (ladder_shape : LadderShape board rank φ) :
     (∀ bp, board bp = some ⟨.Black, .King⟩ → bp.file.val >= 2) := by sorry

-- Re-expresses `applyMove`'s piece-lookup using `Eq` (Prop) rather than the
-- `BEq`/`Bool` form in the definition, so that `if_pos`/`if_neg` and standard
-- `Eq` rewriting tools can be used directly on `(applyMove b src dst) p`.
private lemma applyMove_pieces {n : Nat} (b : Board n) (src dst p : Pos n) :
    (applyMove b src dst) p =
      if p = dst then b src else if p = src then none else b p := by
  show (applyMove b src dst).pieces p = _
  unfold applyMove
  by_cases h1 : p = dst
  · simp [h1]
  · by_cases h2 : p = src
    · simp [h1, h2]
    · simp [h1, h2]

-- After applying nextWhiteMove, the white king sits on column 0. In
-- every phase the king either stays on its starting square (kingPos has
-- column 0) or moves from (rank, 0) to (rank+1, 0); both are column 0.
lemma LadderMove_WhiteKingCol0 {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) :
    let move := nextWhiteMove lsh
    let b'   := applyMove board move.1 move.2
    ∀ pw, b' pw = some ⟨.White, .King⟩ → pw.file.val = 0 := by
  show ∀ pw, (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2) pw
              = some ⟨.White, .King⟩ → pw.file.val = 0
  intro pw hpw
  obtain ⟨_, hK_at, hRb_at, hRa_at, white_pos, _, _, _⟩ := lsh.unfold
  have hbnd := lsh.hRfits
  rw [applyMove_pieces] at hpw
  -- Closes the `pw ≠ dst, pw ≠ src` branch uniformly: pw's piece is
  -- unchanged, so by white_pos pw is one of the three white squares, and
  -- only kingPos = (rank, 0) is consistent with pw being the king.
  have unchanged_case : ∀ (h : board pw = some ⟨.White, .King⟩), pw.file.val = 0 := by
    intro hb
    rcases white_pos pw (.inl hb) with h | h | h
    · rw [h]; rfl
    · rw [h, hRb_at] at hb; simp at hb
    · rw [h, hRa_at] at hb; simp at hb
  cases φ
  case moveRb =>
    by_cases h1 : pw = (nextWhiteMove lsh).2
    · -- pw = dst forces b src = WK, but src = rookBPos has WR.
      rw [if_pos h1,
          show (nextWhiteMove lsh).1 = rookBPos rank .moveRb hbnd from rfl,
          hRb_at] at hpw
      simp at hpw
    · rw [if_neg h1] at hpw
      by_cases h2 : pw = (nextWhiteMove lsh).1
      · rw [if_pos h2] at hpw; simp at hpw
      · rw [if_neg h2] at hpw; exact unchanged_case hpw
  case moveRa =>
    by_cases h1 : pw = (nextWhiteMove lsh).2
    · rw [if_pos h1,
          show (nextWhiteMove lsh).1 = rookAPos rank .moveRa hbnd from rfl,
          hRa_at] at hpw
      simp at hpw
    · rw [if_neg h1] at hpw
      by_cases h2 : pw = (nextWhiteMove lsh).1
      · rw [if_pos h2] at hpw; simp at hpw
      · rw [if_neg h2] at hpw; exact unchanged_case hpw
  case moveK =>
    -- src = K = (rank, 0), dst = (rank+1, 0); both at column 0.
    by_cases h1 : pw = (nextWhiteMove lsh).2
    · rw [h1]; rfl
    · rw [if_neg h1] at hpw
      by_cases h2 : pw = (nextWhiteMove lsh).1
      · rw [if_pos h2] at hpw; simp at hpw
      · rw [if_neg h2] at hpw; exact unchanged_case hpw

-- After applying nextWhiteMove, every (white-king, black-king) pair is
-- separated by at least two files. Combines `LadderMove_WhiteKingCol0`
-- (white king column = 0) with the `LadderShape` invariant on the black
-- king's column (≥ 2), which is preserved because white moves don't
-- relocate black pieces.
lemma LadderMove_KingsApart {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (ladder_shape : LadderShape board rank φ) :
    let move := nextWhiteMove ladder_shape
    let b'   := applyMove board move.1 move.2
    ∀ pw pb : Pos n,
      (b' pw = some ⟨.White, .King⟩ ∧ b' pb = some ⟨.Black, .King⟩) →
      pw.file.val + 2 ≤ pb.file.val := by
  show ∀ pw pb : Pos n,
    ((applyMove board (nextWhiteMove ladder_shape).1
        (nextWhiteMove ladder_shape).2) pw = some ⟨.White, .King⟩ ∧
     (applyMove board (nextWhiteMove ladder_shape).1
        (nextWhiteMove ladder_shape).2) pb = some ⟨.Black, .King⟩) →
    pw.file.val + 2 ≤ pb.file.val
  intro pw pb ⟨hpw, hpb⟩
  obtain ⟨_, hK_at, hRb_at, hRa_at, _, black_loc, _, _⟩ := ladder_shape.unfold
  rw [applyMove_pieces] at hpb
  -- src always carries some white piece (rook in moveRb/moveRa, king in moveK),
  -- so pb cannot equal dst (would force b src = ⟨Black, King⟩).
  have h_src_white :
      ∃ k, board (nextWhiteMove ladder_shape).1 = some ⟨.White, k⟩ := by
    cases φ
    · exact ⟨.Rook, hRb_at⟩
    · exact ⟨.Rook, hRa_at⟩
    · exact ⟨.King, hK_at⟩
  -- Black king's square is unchanged: a white move into an empty target
  -- doesn't relocate black pieces.
  have hb_pb : board pb = some ⟨.Black, .King⟩ := by
    by_cases h1 : pb = (nextWhiteMove ladder_shape).2
    · rw [if_pos h1] at hpb
      obtain ⟨_, hk⟩ := h_src_white
      rw [hk] at hpb; simp at hpb
    · rw [if_neg h1] at hpb
      by_cases h2 : pb = (nextWhiteMove ladder_shape).1
      · rw [if_pos h2] at hpb; simp at hpb
      · rw [if_neg h2] at hpb; exact hpb
  have h_pw_col : pw.file.val = 0 := LadderMove_WhiteKingCol0 ladder_shape pw hpw
  have h_pb_col : 2 ≤ pb.file.val := (black_loc pb hb_pb).2
  omega


-- A position with column < 2 that does not coincide with any of the three
-- white-piece positions (K, Rb, Ra) is empty. The column bound rules out the
-- black king (LadderShape_KingsApart pins it to column ≥ 2); the three
-- inequalities rule out the white pieces (LadderShape's white_pos conjunct).
lemma LadderShape.empty_at {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (lsh : LadderShape board rank φ) (p : Pos n)
    (hcol : p.file.val < 2)
    (hK  : p ≠ kingPos  rank   lsh.hRfits)
    (hRb : p ≠ rookBPos rank φ lsh.hRfits)
    (hRa : p ≠ rookAPos rank φ lsh.hRfits) :
    board p = none := by
  obtain ⟨_, _, _, _, white_pos, _, only_black_king, _⟩ := lsh.unfold
  have black_col := LadderShape_KingsApart lsh
  rcases hb : board p with _ | ⟨c, k⟩
  · rfl
  · exfalso
    cases c with
    | Black =>
      have hk : k = .King := only_black_king p k hb
      subst hk
      have := black_col p hb
      omega
    | White =>
      have hor : board p = some ⟨.White, .King⟩ ∨
                 board p = some ⟨.White, .Rook⟩ := by
        cases k
        · exact .inl hb
        · exact .inr hb
      rcases white_pos p hor with h | h | h
      · exact hK  h
      · exact hRb h
      · exact hRa h

lemma LadderMove_IntoEmptySquare {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (ladder_shape : LadderShape board rank φ) :
    let dst := (nextWhiteMove ladder_shape).2
    board dst = none := by
  show board (nextWhiteMove ladder_shape).2 = none
  apply ladder_shape.empty_at
  · -- dst.2.val < 2 — by inspection of nextWhiteMove (column is 0 or 1).
    cases φ <;> simp [nextWhiteMove, rookBPos, rookAPos]
  all_goals
    -- Three remaining goals are inequalities of the form dst ≠ piecePos.
    -- For each phase, dst differs from the piece on at least one component
    -- (row or column); extracting both .1.val and .2.val and simp-reducing
    -- closes all 9 sub-cases uniformly.
    intro heq
    have h1 := congrArg (fun x : Pos n => x.rank.val) heq
    have h2 := congrArg (fun x : Pos n => x.file.val) heq
    cases φ <;>
      simp [nextWhiteMove, kingPos, rookBPos, rookAPos] at h1 h2



-- after applying nextWhiteMove, every black-occupied square is still a
-- black king. Specialisation of `applyMove_PreservesOnlyBlackKing` to the
-- ladder move; the only-black-king clause is part of `LadderShape`.
lemma LadderMove_PreservesOnlyBlackKing {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (ladder_shape : LadderShape board rank φ) :
    let move := nextWhiteMove ladder_shape
    let b'   := applyMove board move.1 move.2
    ∀ p k, b' p = some ⟨.Black, k⟩ → k = .King := by
  show ∀ p k, (applyMove board (nextWhiteMove ladder_shape).1
                (nextWhiteMove ladder_shape).2) p = some ⟨.Black, k⟩ → k = .King
  obtain ⟨_, _, _, _, _, _, only_bk, _⟩ := ladder_shape.unfold
  exact applyMove_PreservesOnlyBlackKing board _ _ only_bk


-- Phase-agnostic finisher: given the `LadderShape` invariant plus a
-- specific piece at the move's src and a valid move for that piece,
-- conclude `IsLegalMove`. All four conjuncts of `IsLegalMove` are
-- delivered here; only the phase-specific ones (piece, validity)
-- are asked of the caller.
lemma LadderMove_LegalIfMoveValid {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    (piece : PieceType)
    (h_at_src : board (nextWhiteMove lsh).1 = some ⟨board.turn, piece⟩)
    (h_valid  : PieceMoveLogic board
                  (nextWhiteMove lsh).1 (nextWhiteMove lsh).2 piece) :
    IsLegalMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2 := by
  have dst_empty   := LadderMove_IntoEmptySquare lsh
  have b'_only_bk  := LadderMove_PreservesOnlyBlackKing lsh
  have b'_apart    := LadderMove_KingsApart lsh
  obtain ⟨turn_white, _, _, _, _, _, _, legal_start⟩ := lsh.unfold
  refine ⟨piece, h_at_src, h_valid, ?_, ?_, ?_, ?_⟩
  · exact EmptySquare_NotFriendly _ _ dst_empty
  · exact (NoCaputureMove_PreservesKings _ _ _ legal_start dst_empty).1
  · exact (NoCaputureMove_PreservesKings _ _ _ legal_start dst_empty).2
  · -- `applyMove` flips the turn, so the opponent is White.
    have heq :
        (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2).turn.opponent
          = .White := by
      show board.turn.opponent.opponent = .White
      rw [turn_white]; rfl
    rw [heq]
    exact OpponentOnlyKingFarAway_NoCheck _ b'_only_bk b'_apart


-- ============================================================
-- MAIN THEOREM
-- ============================================================
theorem nextWhiteMove_isLegal {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) :
    IsLegalMove board
      (nextWhiteMove lsh).1 (nextWhiteMove lsh).2 := by
  have dst_empty := LadderMove_IntoEmptySquare lsh
  obtain ⟨turn_white, hK, hRb, hRa, _, _, _, _⟩ := lsh.unfold
  cases φ with
  | moveRb =>
    apply LadderMove_LegalIfMoveValid lsh .Rook
    · rw [turn_white]; exact hRb
    · exact RookUp_IsValid _ _ _ rfl rfl
  | moveRa =>
    apply LadderMove_LegalIfMoveValid lsh .Rook
    · rw [turn_white]; exact hRa
    · exact RookUp_IsValid _ _ _ rfl rfl
  | moveK =>
    apply LadderMove_LegalIfMoveValid lsh .King
    · rw [turn_white]; exact hK
    · exact KingUp_IsValid _ _ rfl rfl
