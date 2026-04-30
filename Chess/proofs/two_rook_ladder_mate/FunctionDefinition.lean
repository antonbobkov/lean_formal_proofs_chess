import ChessRules

-- ============================================================
-- Two-Rook Deterministic Ladder Mate
-- ============================================================
-- White has King + two Rooks ("a-file" and "b-file"); Black has only
-- a King. Every cycle of three White plies shifts the white setup up
-- by one rank.
--
-- Invariant (start of cycle, parameterised by base rank R : Fin n):
--   K = (R, 0),  R_b = (R, 1),  R_a = (R+1, 0),  White to move.
--
-- The three plies of a cycle:
--   1. .moveRb : R_b moves up — (R,1) → (R+1,1)
--   2. .moveRa : R_a moves up — (R+1,0) → (R+2,0)
--   3. .moveK  : K moves up   — (R,0) → (R+1,0)
--
-- After the cycle, the setup matches the invariant for R' = R+1.
-- This file formalises the invariant and the deterministic move
-- function consumed via a `LadderShape` proof; preservation and
-- eventual-checkmate theorems are out of scope.


-- ------------------------------------------------------------
-- PHASE TAG
-- ------------------------------------------------------------
inductive LadderPhase
  | moveRb
  | moveRa
  | moveK
  deriving DecidableEq, Repr


-- ------------------------------------------------------------
-- WHITE PIECE POSITIONS (parameterised by base rank R and phase)
-- ------------------------------------------------------------
-- The bound `R.val + 2 < n` is needed because the procedure refers
-- to ranks R, R+1, and R+2; without it some target squares would
-- not exist on the board.
--
-- Mapping:
--   φ        K           R_b          R_a
--   moveRb   (R, 0)      (R, 1)       (R+1, 0)
--   moveRa   (R, 0)      (R+1, 1)     (R+1, 0)
--   moveK    (R, 0)      (R+1, 1)     (R+2, 0)

def kingPos {n : Nat} (rank : Fin n)
    (space_left : rank.val + 2 < n) : Pos n :=
  ⟨rank, ⟨0, by omega⟩⟩

def rookBPos {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (space_left : rank.val + 2 < n) : Pos n :=
  match φ with
  | .moveRb => ⟨rank, ⟨1, by omega⟩⟩
  | .moveRa => ⟨⟨rank.val + 1, by omega⟩, ⟨1, by omega⟩⟩
  | .moveK  => ⟨⟨rank.val + 1, by omega⟩, ⟨1, by omega⟩⟩

def rookAPos {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (space_left : rank.val + 2 < n) : Pos n :=
  match φ with
  | .moveRb => ⟨⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩⟩
  | .moveRa => ⟨⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩⟩
  | .moveK  => ⟨⟨rank.val + 2, by omega⟩, ⟨0, by omega⟩⟩


-- ------------------------------------------------------------
-- INVARIANT
-- ------------------------------------------------------------
-- We use `dite` so the bound `R.val + 2 < n` is *part of* the
-- proposition: `LadderShape` reduces to `False` when the bound
-- fails, and to a plain conjunction when it holds. This keeps the
-- shape decidable without needing a hand-written instance.
def LadderShape {n : Nat} (board : Board n) (rank : Fin n)
    (φ : LadderPhase) : Prop :=
  if space_left : rank.val + 2 < n then
    board.turn = .White ∧
    board (kingPos rank space_left) = some ⟨.White, .King⟩ ∧
    board (rookBPos rank φ space_left) =
        some ⟨.White, .Rook⟩ ∧
    board (rookAPos rank φ space_left) =
        some ⟨.White, .Rook⟩ ∧
    (∀ p, (board p = some ⟨.White, .King⟩ ∨
           board p = some ⟨.White, .Rook⟩) →
          p = kingPos rank space_left ∨
          p = rookBPos rank φ space_left ∨
          p = rookAPos rank φ space_left) ∧
    (∀ bp, board bp = some ⟨.Black, .King⟩ →
           (rookAPos rank φ space_left).rank < bp.rank ∧ 2 ≤ bp.file.val) ∧
    (∀ p k, board p = some ⟨.Black, k⟩ → k = .King) ∧
    IsLegalSetup board
  else False

instance {n : Nat} (board : Board n) (rank : Fin n) (φ : LadderPhase) :
    Decidable (LadderShape board rank φ) := by
  unfold LadderShape; infer_instance


-- ------------------------------------------------------------
-- BOUND-EXTRACTION LEMMA
-- ------------------------------------------------------------
-- `LadderShape` carries the bound `R.val + 2 < n` implicitly: if
-- the bound fails, the proposition reduces to `False`. This lemma
-- pulls the bound out so we can hand it to the move function.
theorem LadderShape.hRfits {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase}
    (ladder_shape_hypothesis : LadderShape board rank φ) :
    rank.val + 2 < n := by
  unfold LadderShape at ladder_shape_hypothesis
  by_cases hbnd : rank.val + 2 < n
  · exact hbnd
  · rw [dif_neg hbnd] at ladder_shape_hypothesis
    exact ladder_shape_hypothesis.elim


-- ------------------------------------------------------------
-- THE NEXT WHITE MOVE
-- ------------------------------------------------------------
-- Given a `LadderShape` proof, return the (src, dst) pair for
-- the unique White move dictated by the procedure. Total — the
-- proof guarantees the bound holds.
def nextWhiteMove {n : Nat} {board : Board n} {rank : Fin n} {φ : LadderPhase}
    (ladder_shape_hypothesis : LadderShape board rank φ) : Pos n × Pos n :=
  have hbnd : rank.val + 2 < n := ladder_shape_hypothesis.hRfits
  match φ with
  | .moveRb => (rookBPos rank .moveRb hbnd, rookBPos rank .moveRa hbnd)
  | .moveRa => (rookAPos rank .moveRa hbnd, rookAPos rank .moveK  hbnd)
  | .moveK  =>
      (kingPos rank hbnd, ⟨⟨rank.val + 1, by omega⟩, ⟨0, by omega⟩⟩)


-- ------------------------------------------------------------
-- APPLY THE NEXT WHITE MOVE
-- ------------------------------------------------------------
-- Returns the board after one White ply. `applyMove` already flips
-- the turn, so the resulting board has Black to move.
def ladderStep {n : Nat} {board : Board n} {rank : Fin n} {φ : LadderPhase}
    (ladder_shape_hypothesis : LadderShape board rank φ) : Board n :=
  let move := nextWhiteMove ladder_shape_hypothesis
  applyMove board move.1 move.2


-- ------------------------------------------------------------
-- PHASE ADVANCEMENT (informational)
-- ------------------------------------------------------------
-- After one White ply, the next phase is given by `nextPhase`.
-- The base rank advances (R → R+1) only after `moveK`.
def nextPhase : LadderPhase → LadderPhase
  | .moveRb => .moveRa
  | .moveRa => .moveK
  | .moveK  => .moveRb


-- ------------------------------------------------------------
-- RANK ADVANCEMENT
-- ------------------------------------------------------------
-- The base rank advances only on the moveK ply; the other two
-- plies keep the same rank.
def nextRank {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (space_left : rank.val + 2 < n) : Fin n :=
  match φ with
  | .moveK => ⟨rank.val + 1, by omega⟩
  | _      => rank


-- ------------------------------------------------------------
-- PRESERVATION THEOREM (statement only)
-- ------------------------------------------------------------
-- After one White ply (ladderStep) and any legal Black reply,
-- the resulting board satisfies LadderShape for the advanced
-- rank and the next phase.
theorem LadderShape.preservation {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    LadderShape
      (applyMove (ladderStep lsh) bsrc bdst)
      (nextRank rank φ lsh.hRfits)
      (nextPhase φ) := by
  sorry


-- ------------------------------------------------------------
-- LADDER STATE
-- ------------------------------------------------------------
-- Bundles the board with its invariant proof so that the
-- one-cycle step function has type `LadderState n → LadderState n`
-- and can be iterated with `^[k]`.
structure LadderState (n : Nat) where
  board : Board n
  rank  : Fin n
  phase : LadderPhase
  shape : LadderShape board rank phase


-- ------------------------------------------------------------
-- TERMINATION / CHECKMATE THEOREM (statement only)
-- ------------------------------------------------------------
-- The ladder forces checkmate for Black in finitely many full cycles
-- (one White ply + one legal Black ply each), regardless of how Black
-- plays.
--
-- `reply` is an arbitrary Black strategy: given the board after the
-- White ply it picks (src, dst).  `hreply` witnesses that every chosen
-- move is legal.  The iteration uses `Function.iterate` (^[k]) on the
-- one-cycle step that advances the LadderState via
-- `LadderShape.preservation`.
theorem ladderMate_termination {n : Nat}
    (s₀    : LadderState n)
    (reply  : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n,
        IsLegalMove (ladderStep s.shape)
                    (reply (ladderStep s.shape)).1
                    (reply (ladderStep s.shape)).2) :
    ∃ k : Nat,
      IsCheckmate
        ((fun s : LadderState n =>
            { board := applyMove (ladderStep s.shape)
                         (reply (ladderStep s.shape)).1
                         (reply (ladderStep s.shape)).2
              rank  := nextRank s.rank s.phase s.shape.hRfits
              phase := nextPhase s.phase
              shape := LadderShape.preservation s.shape (hreply s) })^[k] s₀).board
        .Black := by
  sorry
  /-
  PROOF SKETCH

  ── Core idea: contradiction via rank exhaustion ─────────────────────────────

  Every full cycle (one White ply + one legal Black reply) advances the base
  rank by exactly 1 (via `nextRank` on the `.moveK` ply; the other two plies
  leave the rank unchanged). The `space_left` bound baked into every
  `LadderShape` proof requires `rank.val + 2 < n`. So if the current base rank
  is R the bound says R ≤ n − 3, and after k full cycles the rank is R₀ + k,
  still needing R₀ + k ≤ n − 3.

  This means there is a hard finite ceiling: after at most
      K := n − 2 − s₀.rank.val     (which satisfies 0 ≤ K because s₀.shape.hRfits gives R₀ + 2 < n)
  full cycles the base rank would reach n − 2, making `space_left` false and
  therefore `LadderShape board (n−2) φ` definitionally equal to `False`.

  If checkmate has not yet occurred, `LadderShape.preservation` (together with
  `hreply`) lets us build a valid `LadderState` after each cycle. After K
  cycles we would hold a `LadderState` whose `.shape` field has type
  `LadderShape _ ⟨n−2, …⟩ _`. Unfolding the definition reduces that to `False`,
  and we derive anything — in particular the ∃ k goal — ex falso. So checkmate
  must have occurred strictly before cycle K.

  ── Why the measure is strictly monotone ─────────────────────────────────────

  Define the *headroom* of a `LadderState s` as `n − 2 − s.rank.val` (a Nat,
  which is always well-defined because `s.shape.hRfits` gives `s.rank.val + 2 < n`).
  After one full cycle `nextRank` replaces `s.rank` with `⟨s.rank.val + 1, _⟩`,
  strictly decreasing the headroom. Headroom ≥ 0 because it lives in ℕ, so the
  process terminates in at most K steps.

  ── Formal proof structure ────────────────────────────────────────────────────

  Let `step` be the one-cycle function appearing in the goal (let-bind it for
  clarity). The concrete proof can be written as induction on the headroom:

  (1) Base case (headroom = 0, i.e., rank = n − 2):
      Unfold `LadderShape` at `s.shape`; the `dif_neg` branch fires because
      `n − 2 + 2 < n` is false, so `s.shape : False`.  Apply `s.shape.elim`.
      (This base case is vacuously true — it proves the ∃ k goal from False.)

  (2) Inductive step (headroom = h + 1):
      Either the board after the White ply is already checkmate for Black …
        · If `IsCheckmate (ladderStep s.shape).board .Black` holds, use k = 0.
          (One subtle point: the k in the goal indexes full cycles White+Black,
          so k = 0 means the board is already checkmate before any Black reply.
          Confirm the iteration at 0 returns `s₀.board` untouched — that's
          `Function.iterate_zero` — and close with the checkmate witness.)
        … or it is not checkmate, so a legal Black reply exists …
        · If not, `hreply s` gives a legal Black reply.  Apply
          `LadderShape.preservation s.shape (hreply s)` to obtain `s' : LadderState n`
          with `s'.rank.val = s.rank.val + 1` and headroom h.
        · Apply the inductive hypothesis to `s'` with the same `reply` and
          the same `hreply` (which quantifies over all `LadderState`s) to get
          `k'` and the checkmate proof for `(step^[k'] s').board`.
        · Set k = k' + 1 and rewrite `step^[k'+1] s₀ = step^[k'] (step s₀) = step^[k'] s'`
          using `Function.iterate_succ_apply`.

  ── Decidability of `IsCheckmate` ────────────────────────────────────────────

  To perform the case split "is the board checkmate or not" we need
  `Decidable (IsCheckmate b .Black)`.  `IsCheckmate` is built from
  `IsInCheck` (which is a finite conjunction of board-lookup equalities) and
  `∀ src dst, ¬ IsLegalMove b src dst` (a finite universal over `Fin n × Fin n`,
  hence decidable on a finite board).  Both facts should follow from
  `DecidableEq` on `Piece` and finiteness of `Fin n`.

  ── Choosing k explicitly ────────────────────────────────────────────────────

  If we want a computable witness rather than a classical existence proof we
  can instead run the iteration up to the hard bound K and check at each step:

      decide_ladder_mate : ∀ s : LadderState n,
          ∃ k ≤ n − 2 − s.rank.val,
            IsCheckmate (step^[k] s).board .Black

  proved by Nat.rec on the headroom, using decidability of `IsCheckmate` at each
  step to pick k = 0 or recurse.  The bound k ≤ K is a pleasant bonus: it gives
  a concrete worst-case number of full cycles.

  ── What `LadderShape.preservation` must actually show ───────────────────────

  The inductive step leans entirely on `preservation` (currently `sorry`'d).
  That theorem needs to establish:
  · The white pieces stay in their prescribed slots after the White ply.
  · Any legal Black reply cannot capture a white rook or king (the rooks sit
    on the file boundary the black king cannot cross, and the king is protected).
  · The black king remains strictly above `rookAPos` rank after the Black reply.
  · The board remains a legal setup.
  Proving preservation is the hard part; once it is in place the termination
  argument above is almost purely combinatorial.
  -/
