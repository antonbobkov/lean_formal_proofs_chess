import FunctionDefinition
import HelperLemmas

-- ============================================================
-- MAIN THEOREM
-- ============================================================
theorem nextWhiteMove_isLegal {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) :
    IsLegalMove board
      (nextWhiteMove lsh).1 (nextWhiteMove lsh).2 := by sorry
  /-
  PROOF SKETCH (in words) — phase-agnostic version

  ── Goal shape ───────────────────────────────────────────────────────────────
  Unfolding `IsLegalMove`, we must produce a `piece : PieceType` and prove
      (a) board src = some ⟨board.turn, piece⟩
      (b) PieceMoveLogic board src dst piece
      (c) ¬ IsFriendlyOccupied board dst
      (d) IsLegalSetup (applyMove board src dst)
  where (src, dst) = nextWhiteMove lsh.

  ── Shared setup ─────────────────────────────────────────────────────────────
  Unfold `LadderShape` at `lsh` (the bound `rank.val + 2 < n` is delivered by
  `LadderShape.hRfits`). From `lsh` we extract once:
    · `turn_white   : board.turn = .White`
    · `legal_start  : IsLegalSetup board`
  And from the helper lemmas we extract once:
    · `dst_empty    : board dst = none`
                     — `LadderMove_IntoEmptySquare lsh`
    · `b'_only_bk   : ∀ p k, b' p = some ⟨.Black, k⟩ → k = .King`
                     — `LadderMove_PreservesOnlyBlackKing lsh`
    · `b'_kings_apart : ∀ pw pb, (b' pw = WK ∧ b' pb = BK) → pw.1.val + 2 ≤ pb.1.val`
                     — `LadderMove_KingsRowsApart lsh`
  where `b' := applyMove board src dst`.

  Key geometric fact, uniform across all three phases: by inspection of
  `nextWhiteMove`, in every case `src.1.val + 1 = dst.1.val` and
  `src.2 = dst.2` — the white piece moves up exactly one rank, same file.

  ── (a) Piece at src ─────────────────────────────────────────────────────────
  We provide the piece kind dictated by the phase (rook for .moveRb / .moveRa,
  king for .moveK). In each phase the corresponding `kingPos` / `rookBPos` /
  `rookAPos` conjunct of `LadderShape` says exactly that this piece sits on
  `src`. Combined with `turn_white`, this gives (a). This is the only part
  where we even need to mention φ; the remaining steps cite phase-agnostic
  helper lemmas.

  ── (b) Piece move logic ─────────────────────────────────────────────────────
  Splits on the piece kind we chose, but symmetrically:

    Rook phases: `RookUpEmpty_IsValid board src dst dst_empty (by rfl)` —
      `src.1.val + 1 = dst.1.val` reduces to `rfl` after the match, and
      `dst_empty` is in hand.

    King phase: `KingUpEmpty_IsValid src dst (by rfl) (by rfl)` — the
      same-file and one-step-up facts are again `rfl` post-match.

  Both helpers have the same shape, so this conjunct is uniform up to which
  validity predicate is being proved.

  ── (c) ¬ IsFriendlyOccupied board dst ──────────────────────────────────────
  One citation: `EmptySquare_NotFriendly board dst dst_empty`. No phase
  reasoning at all.

  ── (d) IsLegalSetup (applyMove board src dst) ──────────────────────────────
  Unfold `IsLegalSetup`. We must show three things about `b'`:

    (d1) ∃! wp, b' wp = some ⟨.White, .King⟩
    (d2) ∃! bp, b' bp = some ⟨.Black, .King⟩
    (d3) ¬ IsCheck b' b'.turn.opponent
         `applyMove` flips the turn to Black, so the opponent is White.

    (d1) ∧ (d2): `NoCaputureMove_PreservesKings board src dst legal_start
                  dst_empty` returns exactly this pair.

    (d3): `OpponentOnlyKing_NoCheck b' b'_only_bk b'_kings_apart`. Both
          hypotheses are pre-extracted helper-lemma outputs; nothing here is
          phase-specific.

  ── Why this is phase-agnostic ───────────────────────────────────────────────
  After the shared setup all four of (b)'s helpers, (c)'s helper, and both of
  (d)'s helpers consume `lsh` directly without examining φ. The only place φ
  appears is (a), where it picks `piece := .Rook` versus `piece := .King` and
  selects which `LadderShape` conjunct to cite. The rank-gap arithmetic that
  used to differ per phase has been absorbed into `NextWhiteMove_KingsRowsApart`,
  and the "black squares stay black-king-only" reasoning into
  `LadderMove_PreservesOnlyBlackKing`.

  ── Skeleton of the actual Lean proof ────────────────────────────────────────
      have hbnd        := lsh.hRfits
      have dst_empty   := LadderMove_IntoEmptySquare lsh
      have b'_only_bk  := LadderMove_PreservesOnlyBlackKing lsh
      have b'_apart    := LadderMove_KingsRowsApart lsh
      -- pull `turn_white` and `legal_start` out of `lsh` by unfolding
      -- LadderShape and using `dif_pos hbnd`.
      cases φ
      all_goals
        refine ⟨_, ?_, ?_, ?_, ?_⟩
        · -- (a): piece at src, from LadderShape conjunct + turn_white
          sorry
        · -- (b): RookUpEmpty_IsValid / KingUpEmpty_IsValid
          sorry
        · -- (c): EmptySquare_NotFriendly _ _ dst_empty
          exact EmptySquare_NotFriendly _ _ dst_empty
        · -- (d): IsLegalSetup
          refine ⟨?_, ?_, ?_⟩
          · exact (NoCaputureMove_PreservesKings _ _ _ legal_start dst_empty).1
          · exact (NoCaputureMove_PreservesKings _ _ _ legal_start dst_empty).2
          · exact OpponentOnlyKing_NoCheck _ b'_only_bk b'_apart
  Only the two `sorry`s above carry any phase content; the rest is a single
  uniform skeleton that works for all three φ.
  -/
