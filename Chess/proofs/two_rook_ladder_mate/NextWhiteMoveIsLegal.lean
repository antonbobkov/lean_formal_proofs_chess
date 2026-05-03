import FunctionDefinition
import HelperLemmas

-- ============================================================
-- LOCAL HELPER LEMMAS
-- ============================================================
-- These bundle the phase-uniform tail of the legality proof so the
-- main theorem only has to handle the phase-specific bits (which
-- piece is at src and which validity helper to invoke).

-- No white piece sits strictly above `rookAPos` on its file (file 0).
-- Follows from `LadderShape`'s `white_pos` clause: every white piece is
-- one of K, R_b, R_a, and none of those occupies a square above R_a on
-- file 0 in any phase.
lemma LadderShape_NoWhiteAboveRa {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (lsh : LadderShape board rank φ) (p : Pos n)
    (hfile : p.file.val = 0)
    (habove : (rookAPos rank φ lsh.hRfits).rank.val < p.rank.val) :
    ∀ k, board p ≠ some ⟨.White, k⟩ := by
  intro k hp
  obtain ⟨_, _, _, _, white_pos, _, _, _⟩ := lsh.unfold
  rcases white_pos p ⟨k, hp⟩ with hK | hRb | hRa
  · -- p = kingPos = (rank, 0); but habove forces p.rank.val > rookAPos.rank.val ≥ rank.val + 1.
    have hpr : p.rank.val = rank.val := by rw [hK]; simp [kingPos]
    have hRa_rank : rank.val + 1 ≤ (rookAPos rank φ lsh.hRfits).rank.val := by
      cases φ <;> simp [rookAPos]
    omega
  · -- p = rookBPos, which has file 1; contradicts hfile = 0.
    have hpf : p.file.val = 1 := by
      rw [hRb]; cases φ <;> simp [rookBPos]
    omega
  · -- p = rookAPos, but habove says p.rank > rookAPos.rank.
    rw [hRa] at habove
    omega

-- No white piece sits strictly above `rookBPos` on its file (file 1).
-- Same shape as `LadderShape_NoWhiteAboveRa`.
lemma LadderShape_NoWhiteAboveRb {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (lsh : LadderShape board rank φ) (p : Pos n)
    (hfile : p.file.val = 1)
    (habove : (rookBPos rank φ lsh.hRfits).rank.val < p.rank.val) :
    ∀ k, board p ≠ some ⟨.White, k⟩ := by
  intro k hp
  obtain ⟨_, _, _, _, white_pos, _, _, _⟩ := lsh.unfold
  rcases white_pos p ⟨k, hp⟩ with hK | hRb | hRa
  · -- p = kingPos has file 0, contradicts hfile = 1.
    have hpf : p.file.val = 0 := by rw [hK]; simp [kingPos]
    omega
  · -- p = rookBPos, but habove says p.rank > rookBPos.rank.
    rw [hRb] at habove
    omega
  · -- p = rookAPos has file 0, contradicts hfile = 1.
    have hpf : p.file.val = 0 := by
      rw [hRa]; cases φ <;> simp [rookAPos]
    omega

-- Geometric core of the file-N InCheck lemmas. Given a white rook on the
-- same file as the black king, strictly below it, with no white piece
-- above the rook on that file, the black king is in check.
-- The "no piece strictly between" conjunct of `ValidRookMove` is closed
-- by combining `no_white_above` (rules out white) with the unique-black-
-- king clause of `IsLegalSetup` (the only black piece is bp itself, which
-- lies above the strict-between range).
lemma LadderShape_RookSeesBlackKing_InCheck {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    (r bp : Pos n)
    (hr_at : board r = some ⟨.White, .Rook⟩)
    (hbp : board bp = some ⟨.Black, .King⟩)
    (hr_below : r.rank.val < bp.rank.val)
    (hr_same_file : r.file = bp.file)
    (no_white_above : ∀ q, q.file = r.file → r.rank.val < q.rank.val →
                      ∀ k, board q ≠ some ⟨.White, k⟩) :
    IsCheck board .Black := by
  obtain ⟨_, _, _, _, _, _, only_bk, _, ⟨bkW, _, hbk_uniq⟩, _⟩ := lsh.unfold
  refine ⟨bp, hbp, r, .inl ⟨hr_at, ?_, .inr ⟨hr_same_file, ?_⟩⟩⟩
  · -- r ≠ bp (different ranks)
    intro heq
    have : r.rank.val = bp.rank.val := by rw [heq]
    omega
  · intro q hqfile hbet
    have hq_above : r.rank.val < q.rank.val := by unfold Between at hbet; omega
    have no_white := no_white_above q hqfile hq_above
    rcases hboard : board q with _ | ⟨c, kind⟩
    · rfl
    · exfalso
      cases c with
      | White => exact no_white kind hboard
      | Black =>
        have hk : kind = .King := only_bk q kind hboard
        subst hk
        have h_q_eq : q = bkW := hbk_uniq q hboard
        have h_bp_eq : bp = bkW := hbk_uniq bp hbp
        rw [h_q_eq.trans h_bp_eq.symm] at hbet
        unfold Between at hbet
        omega

-- A black king on file 0 would be in check from `rookAPos`.
lemma LadderShape_BlackKingFile0_InCheck {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    (bp : Pos n) (hbp : board bp = some ⟨.Black, .King⟩) (hfile : bp.file.val = 0) :
    IsCheck board .Black := by
  obtain ⟨_, _, _, hRa_at, _, black_loc, _, _⟩ := lsh.unfold
  have h := lsh.hRfits
  have hRa_file : (rookAPos rank φ h).file.val = 0 := by cases φ <;> simp [rookAPos]
  refine LadderShape_RookSeesBlackKing_InCheck lsh (rookAPos rank φ h) bp
    hRa_at hbp (black_loc bp hbp) (Fin.ext (by omega)) ?_
  intro q hqfile hq_above k hp
  have : q.file.val = (rookAPos rank φ h).file.val := by rw [hqfile]
  exact LadderShape_NoWhiteAboveRa lsh q (by omega) hq_above k hp

-- A black king on file 1 would be in check from `rookBPos`.
-- rookBPos.rank ≤ rookAPos.rank in every phase, so the rookAPos rank
-- bound from `LadderShape` propagates to rookBPos.
lemma LadderShape_BlackKingFile1_InCheck {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    (bp : Pos n) (hbp : board bp = some ⟨.Black, .King⟩) (hfile : bp.file.val = 1) :
    IsCheck board .Black := by
  obtain ⟨_, _, hRb_at, _, _, black_loc, _, _⟩ := lsh.unfold
  have h := lsh.hRfits
  have hRa_rank_lt : (rookAPos rank φ h).rank.val < bp.rank.val := black_loc bp hbp
  have hRb_le_Ra : (rookBPos rank φ h).rank.val ≤ (rookAPos rank φ h).rank.val := by
    cases φ <;> simp [rookBPos, rookAPos]
  have hRb_file : (rookBPos rank φ h).file.val = 1 := by cases φ <;> simp [rookBPos]
  refine LadderShape_RookSeesBlackKing_InCheck lsh (rookBPos rank φ h) bp
    hRb_at hbp (by omega) (Fin.ext (by omega)) ?_
  intro q hqfile hq_above k hp
  have : q.file.val = (rookBPos rank φ h).file.val := by rw [hqfile]
  exact LadderShape_NoWhiteAboveRb lsh q (by omega) hq_above k hp

-- The black king is at least two files from the white king. Files 0 and 1
-- would each leave Black in check (via the file-N InCheck helpers), but
-- IsLegalSetup says Black (the side not to move) is not in check.
lemma LadderShape_KingsApart {n : Nat} {board : Board n} {rank : Fin n}
  {φ : LadderPhase} (ladder_shape : LadderShape board rank φ) :
     (∀ bp, board bp = some ⟨.Black, .King⟩ → bp.file.val >= 2) := by
  intro bp hbp
  obtain ⟨turn_white, _, _, _, _, _, _, _, _, h_no_check⟩ := ladder_shape.unfold
  -- turn = White, so the side-not-to-move (in `IsLegalSetup`) is Black.
  have h_black_no_check : ¬ IsCheck board .Black := by
    rw [turn_white] at h_no_check; exact h_no_check
  by_contra hge
  rcases (show bp.file.val = 0 ∨ bp.file.val = 1 by omega) with h0 | h1
  · exact h_black_no_check
      (LadderShape_BlackKingFile0_InCheck ladder_shape bp hbp h0)
  · exact h_black_no_check
      (LadderShape_BlackKingFile1_InCheck ladder_shape bp hbp h1)

-- Re-expresses `applyMove`'s piece-lookup using `Eq` (Prop) rather than the
-- `BEq`/`Bool` form in the definition, so that `if_pos`/`if_neg` and standard
-- `Eq` rewriting tools can be used directly on `(applyMove b src dst) p`.
lemma applyMove_pieces {n : Nat} (b : Board n) (src dst p : Pos n) :
    (applyMove b src dst) p =
      if p = dst then b src else if p = src then none else b p := by
  show (applyMove b src dst).pieces p = _
  unfold applyMove
  by_cases h1 : p = dst
  · simp [h1]
  · by_cases h2 : p = src
    · simp [h2]
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
    rcases white_pos pw ⟨.King, hb⟩ with h | h | h
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
  have h_pb_col : 2 ≤ pb.file.val := LadderShape_KingsApart ladder_shape pb hb_pb
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
      rcases white_pos p ⟨k, hb⟩ with h | h | h
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
