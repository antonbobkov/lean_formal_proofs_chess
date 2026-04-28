import Mathlib.Logic.ExistsUnique

-- ============================================================
-- Mini Chess: n×n board, Kings and Rooks only
-- ============================================================
-- This file defines the types and logic for a tiny chess variant.
-- It is meant to be read top-to-bottom: each definition builds
-- on the ones above it.
--
-- The chess predicates (Between, ValidKingMove, IsCheck, ...) are
-- written as `Prop` rather than `Bool`.  They stay executable via
-- `Decidable` instances, so `#guard` and `decide` still work, but
-- proofs about them manipulate `∧`/`∨`/`∃`/`¬` directly instead of
-- shuffling `= true` / `Bool.false_eq_true` everywhere.


-- ------------------------------------------------------------
-- INDUCTIVE TYPES
-- ------------------------------------------------------------
-- `inductive` is how you define a type by listing all its possible
-- forms (called "constructors"). It's like an enum in other languages,
-- but more powerful.
--
-- `deriving DecidableEq` tells Lean to automatically generate a proof
-- that equality between two Color values is always decidable — meaning
-- Lean can always compute whether two values are equal. This is what
-- makes `==` work on Color values.
--
-- `deriving Repr` generates a way to print Color values (useful for
-- `#eval` in the editor, which lets you run expressions interactively).
inductive Color where
  | White
  | Black
  deriving DecidableEq, Repr

-- `Color.opponent` uses *pattern matching* to define the function.
-- The dot syntax `.White` is shorthand for `Color.White` — Lean can
-- infer the type from context.
-- The `→` arrow means "function from ... to ...".
def Color.opponent : Color → Color
  | .White => .Black
  | .Black => .White

-- Same idea: a type with exactly two constructors.
inductive PieceType where
  | King
  | Rook
  deriving DecidableEq, Repr


-- ------------------------------------------------------------
-- STRUCTURES
-- ------------------------------------------------------------
-- `structure` defines a record type — a bundle of named fields.
-- Unlike `inductive`, it has exactly one constructor (built automatically).
-- You can read `.color` and `.kind` off any `Piece` value.
--
-- Because `Color` and `PieceType` already have `DecidableEq`,
-- Lean can derive it for `Piece` too — two pieces are equal when
-- both their color and kind are equal.
structure Piece where
  color : Color
  kind  : PieceType
  deriving DecidableEq, Repr


-- ------------------------------------------------------------
-- TYPE ALIASES
-- ------------------------------------------------------------
-- `abbrev` (short for "abbreviation") creates a *transparent* alias.
-- "Transparent" means Lean treats `Pos n` as exactly the same type as
-- `Fin n × Fin n` everywhere — no conversion is needed.
--
-- `Fin n` is the type of natural numbers that are *guaranteed* to be
-- less than n (i.e., 0 through n−1). It carries a proof of the bound
-- inside it, so out-of-range values literally cannot be constructed.
--
-- `×` is the product (pair) type. `Fin n × Fin n` is a pair of such
-- numbers — one for the row, one for the column. Together they name
-- one of the n² squares on an n×n board.
abbrev Pos (n : Nat) := Fin n × Fin n

-- A `Board n` bundles two pieces of state for an n×n position:
--   * `pieces`: a function from positions to occupants — `none` for empty,
--     `some piece` for an occupied square. (`Option T` is either `none`
--     or `some v` — Lean's built-in nullable type.)
--   * `turn`: whose move it is right now.
--
-- The `CoeFun` instance below lets us still write `b p` to look up the
-- piece at `p`; Lean coerces the structure to its underlying function.
structure Board (n : Nat) where
  pieces : Pos n → Option Piece
  turn   : Color

instance {n : Nat} : CoeFun (Board n) (fun _ => Pos n → Option Piece) where
  coe b := b.pieces


-- ------------------------------------------------------------
-- ENUMERATE ALL SQUARES
-- ------------------------------------------------------------
-- `List.finRange n` produces [⟨0,_⟩, ⟨1,_⟩, ..., ⟨n-1,_⟩] : List (Fin n).
-- The underscore `_` stands for the proof that each value is < n;
-- Lean fills that in automatically.
--
-- `flatMap f xs` applies `f` to every element of `xs` and concatenates
-- the resulting lists. Here we use it to build every (row, col) pair:
-- for each row r, for each col c, emit the pair (r, c).
-- This gives all n² squares in row-major order.
def allPositions (n : Nat) : List (Pos n) :=
  (List.finRange n).flatMap fun r =>
    (List.finRange n).map fun c => (r, c)


-- ------------------------------------------------------------
-- HELPER: every position is in allPositions
-- ------------------------------------------------------------
-- Used both by proofs and (crucially) by the Decidable instances
-- below, which reduce `∀ p : Pos n, …` and `∃ p : Pos n, …` to the
-- list-bounded versions over `allPositions n`.
theorem mem_allPositions {n : Nat} (p : Pos n) : p ∈ allPositions n := by
  obtain ⟨r, c⟩ := p
  unfold allPositions
  rw [List.mem_flatMap]
  refine ⟨r, List.mem_finRange r, ?_⟩
  rw [List.mem_map]
  exact ⟨c, List.mem_finRange c, rfl⟩


-- ------------------------------------------------------------
-- DECIDABILITY OVER POSITIONS
-- ------------------------------------------------------------
-- `Pos n` is finite, so any decidable predicate over it gives a
-- decidable forall/exists.  We bridge through `allPositions n` —
-- core Lean already knows how to decide `∀ x ∈ l, …` and `∃ x ∈ l, …`.
instance instDecidableForallPos {n : Nat} (P : Pos n → Prop) [DecidablePred P] :
    Decidable (∀ p : Pos n, P p) :=
  decidable_of_iff (∀ p ∈ allPositions n, P p)
    ⟨fun h p => h p (mem_allPositions p), fun h p _ => h p⟩

instance instDecidableExistsPos {n : Nat} (P : Pos n → Prop) [DecidablePred P] :
    Decidable (∃ p : Pos n, P p) :=
  decidable_of_iff (∃ p ∈ allPositions n, P p)
    ⟨fun ⟨p, _, hp⟩ => ⟨p, hp⟩, fun ⟨p, hp⟩ => ⟨p, mem_allPositions p, hp⟩⟩


-- ------------------------------------------------------------
-- HELPER: is x strictly between a and b on one axis?
-- ------------------------------------------------------------
-- We need this to check whether a piece blocks a rook's line of sight.
-- The arguments `a`, `b`, `x` are all `Fin n` values (coordinates).
--
-- `.val` extracts the underlying `Nat` from a `Fin n`.  We use plain
-- `Nat` comparisons — no subtraction, which is important because
-- `Nat` subtraction saturates at 0 (e.g. `2 - 5 = 0`) and would give
-- wrong answers here.
--
-- `min` / `max` let us handle both orderings of `a` and `b` uniformly:
-- `Between 3 1 2` and `Between 1 3 2` are both true.
def Between {n : Nat} (a b x : Fin n) : Prop :=
  min a.val b.val < x.val ∧ x.val < max a.val b.val

instance {n : Nat} (a b x : Fin n) : Decidable (Between a b x) := by
  unfold Between; infer_instance


-- ------------------------------------------------------------
-- ROOK ATTACK CHECK
-- ------------------------------------------------------------
-- A rook attacks along its entire rank (row) or file (column),
-- stopping at the first piece it hits.
--
-- `ValidRookMove b src tgt` holds iff `src ≠ tgt` and either
--   * src and tgt share a row, with no occupied square strictly
--     between their columns on that row; or
--   * src and tgt share a column, with no occupied square strictly
--     between their rows on that column.
def ValidRookMove {n : Nat} (b : Board n) (src tgt : Pos n) : Prop :=
  src ≠ tgt ∧
  ((src.1 = tgt.1 ∧ ∀ p : Pos n, p.1 = src.1 → Between src.2 tgt.2 p.2 → b p = none)
   ∨ (src.2 = tgt.2 ∧ ∀ p : Pos n, p.2 = src.2 → Between src.1 tgt.1 p.1 → b p = none))

instance {n : Nat} (b : Board n) (src tgt : Pos n) : Decidable (ValidRookMove b src tgt) := by
  unfold ValidRookMove; infer_instance


-- ------------------------------------------------------------
-- WITHIN-ONE HELPER
-- ------------------------------------------------------------
-- True when |a - b| ≤ 1.  Written symmetrically using `max`/`min` so
-- that `WithinOne a b ↔ WithinOne b a` follows directly from
-- `Nat.max_comm`/`Nat.min_comm`.  Equivalent to
-- `a = b ∨ a + 1 = b ∨ b + 1 = a`.
def WithinOne (a b : Nat) : Prop :=
  max a b - min a b ≤ 1

instance (a b : Nat) : Decidable (WithinOne a b) := by
  unfold WithinOne; infer_instance


-- ------------------------------------------------------------
-- KING ATTACK CHECK
-- ------------------------------------------------------------
-- A king attacks all squares immediately adjacent to it — up to 8
-- squares, one step in any direction (including diagonals).
def ValidKingMove {n : Nat} (src tgt : Pos n) : Prop :=
  src ≠ tgt ∧ WithinOne src.1.val tgt.1.val ∧ WithinOne src.2.val tgt.2.val

instance {n : Nat} (src tgt : Pos n) : Decidable (ValidKingMove src tgt) := by
  unfold ValidKingMove; infer_instance


-- ------------------------------------------------------------
-- FIND THE KING
-- ------------------------------------------------------------
-- Scans all squares and returns the position of the first King of
-- color `c` it finds, or `none` if there is no such king on the board.
def findKing {n : Nat} (b : Board n) (c : Color) : Option (Pos n) :=
  (allPositions n).find? fun p => b p == some ⟨c, .King⟩


-- ------------------------------------------------------------
-- IS THE KING IN CHECK?
-- ------------------------------------------------------------
-- `IsCheck b c` says: there is a king of color `c` somewhere, and
-- some opponent piece attacks its square.  We split on the opponent
-- piece's kind explicitly to keep the statement first-order in the
-- decidable atoms.
def IsCheck {n : Nat} (b : Board n) (c : Color) : Prop :=
  ∃ kingPos, b kingPos = some ⟨c, .King⟩ ∧
    ∃ p,
      (b p = some ⟨c.opponent, .Rook⟩ ∧ ValidRookMove b p kingPos) ∨
      (b p = some ⟨c.opponent, .King⟩ ∧ ValidKingMove p kingPos)

instance {n : Nat} (b : Board n) (c : Color) : Decidable (IsCheck b c) := by
  unfold IsCheck; infer_instance


-- ------------------------------------------------------------
-- APPLY A MOVE
-- ------------------------------------------------------------
-- Relocates the piece at `src` to `dst`, removing whatever was at `dst`
-- (a capture). Every other square is unchanged. The turn flips to the
-- opponent — that's the move-counter half of "applying a move".
def applyMove {n : Nat} (b : Board n) (src dst : Pos n) : Board n where
  pieces p := if p == dst then b src else if p == src then none else b p
  turn := b.turn.opponent


-- ------------------------------------------------------------
-- MOVE TARGET GENERATION
-- ------------------------------------------------------------
-- For each piece type, compute the squares it can move to from `src`
-- on board `b` for color `c`.  These are purely geometric: we do NOT
-- yet filter out moves that leave the king in check; `IsCheckmate`
-- does that via `IsCheck`.
--
-- `List.filter` takes a `Bool` predicate, so we turn the `Prop`-valued
-- attack predicates into `Bool` with `decide`.
def kingMoveTargets {n : Nat} (b : Board n) (src : Pos n) (c : Color) : List (Pos n) :=
  (allPositions n).filter fun dst =>
    decide (ValidKingMove src dst) &&
    match b dst with
    | some p => p.color != c
    | none   => true

def rookMoveTargets {n : Nat} (b : Board n) (src : Pos n) (c : Color) : List (Pos n) :=
  (allPositions n).filter fun dst =>
    decide (ValidRookMove b src dst) &&
    match b dst with
    | some p => p.color != c
    | none   => true


-- ------------------------------------------------------------
-- IS THE KING IN CHECKMATE?
-- ------------------------------------------------------------
-- `IsCheckmate b c` holds when `c`'s king is in check and every
-- candidate move of every friendly piece leaves the king still in
-- check.  We unfold the quantification over the moving piece into
-- two implications (King / Rook) so each conjunct stays decidable.
def IsCheckmate {n : Nat} (b : Board n) (c : Color) : Prop :=
  IsCheck b c ∧
  ∀ src,
    (b src = some ⟨c, .King⟩ →
      ∀ dst ∈ kingMoveTargets b src c, IsCheck (applyMove b src dst) c) ∧
    (b src = some ⟨c, .Rook⟩ →
      ∀ dst ∈ rookMoveTargets b src c, IsCheck (applyMove b src dst) c)

instance {n : Nat} (b : Board n) (c : Color) : Decidable (IsCheckmate b c) := by
  unfold IsCheckmate; infer_instance


-- ------------------------------------------------------------
-- IS THE SETUP LEGAL?
-- ------------------------------------------------------------
-- A legal setup has exactly one White King, exactly one Black King,
-- and the player whose turn it ISN'T is not in check — otherwise the
-- side that just moved would have left the opponent in a check they
-- failed to address (or delivered a check then handed the move back).
-- "Kings not adjacent" is *not* a separate clause: it follows from the
-- no-check condition (see `IsLegalSetup.kings_not_adjacent` in
-- `proofs/BasicProofs.lean`).
def IsLegalSetup {n : Nat} (b : Board n) : Prop :=
  (∃! wp : Pos n, b wp = some ⟨.White, .King⟩) ∧
  (∃! bp : Pos n, b bp = some ⟨.Black, .King⟩) ∧
  ¬ IsCheck b b.turn.opponent

instance {n : Nat} (b : Board n) : Decidable (IsLegalSetup b) := by
  unfold IsLegalSetup ExistsUnique; infer_instance


-- ------------------------------------------------------------
-- IS A MOVE LEGAL?
-- ------------------------------------------------------------
-- `IsLegalMove b src dst` holds when:
--   * the piece at `src` belongs to the side to move (`b.turn`), and
--     its movement is geometrically valid (king step or clear rook line); and
--   * the resulting position satisfies `IsLegalSetup` — in particular,
--     the moving side's king is not left in check.
def IsLegalMove {n : Nat} (b : Board n) (src dst : Pos n) : Prop :=
  ((b src = some ⟨b.turn, .King⟩ ∧ ValidKingMove src dst) ∨
   (b src = some ⟨b.turn, .Rook⟩ ∧ ValidRookMove b src dst)) ∧
  IsLegalSetup (applyMove b src dst)

instance {n : Nat} (b : Board n) (src dst : Pos n) : Decidable (IsLegalMove b src dst) := by
  unfold IsLegalMove; infer_instance
