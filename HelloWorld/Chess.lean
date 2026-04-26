-- ============================================================
-- Mini Chess: n×n board, Kings and Rooks only
-- ============================================================
-- This file defines the types and logic for a tiny chess variant.
-- It is meant to be read top-to-bottom: each definition builds
-- on the ones above it.


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

-- A `Board n` is a *function* from positions to pieces on an n×n board.
-- Lean lets you use functions as data structures. Given any square,
-- the board tells you what's on it: `none` for empty, `some piece`
-- for an occupied square.
-- `Option T` is either `none` or `some v` where `v : T` — Lean's
-- built-in way to represent optional / nullable values.
abbrev Board (n : Nat) := Pos n → Option Piece


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
-- HELPER: is x strictly between a and b on one axis?
-- ------------------------------------------------------------
-- We need this to check whether a piece blocks a rook's line of sight.
-- The arguments `a`, `b`, `x` are all `Fin n` values (coordinates).
--
-- `.val` extracts the underlying `Nat` (natural number) from a `Fin n`.
-- We then use plain `Nat` comparisons — no subtraction needed, which is
-- important because `Nat` subtraction saturates at 0 (e.g. `2 - 5 = 0`)
-- and would give wrong answers here.
--
-- `min` / `max` let us handle both orderings of `a` and `b` uniformly.
-- For example, `between 3 1 2` and `between 1 3 2` both return `true`.
def between {n : Nat} (a b x : Fin n) : Bool :=
  let lo := min a.val b.val
  let hi := max a.val b.val
  lo < x.val && x.val < hi


-- ------------------------------------------------------------
-- ROOK ATTACK CHECK
-- ------------------------------------------------------------
-- A rook attacks along its entire rank (row) or file (column),
-- stopping at the first piece it hits.
--
-- Parameters:
--   b   — the board (tells us what occupies each square)
--   src — the rook's current position
--   tgt — the square we're asking about (e.g. where the king stands)
--
-- Returns `true` if the rook at `src` can see (attack) `tgt`.
def rookAttacks {n : Nat} (b : Board n) (src tgt : Pos n) : Bool :=
  -- A rook does not attack its own square.
  if src == tgt then false
  else
    -- Destructure the pairs into named row/column coordinates.
    -- `let (sr, sc) := src` is pattern-matching on a pair.
    let (sr, sc) := src   -- source row, source column
    let (tr, tc) := tgt   -- target row, target column
    if sr == tr then
      -- Same row: the rook slides horizontally.
      -- We check whether any square on that row sits strictly between
      -- the two column indices and is occupied.
      -- `!` is boolean NOT; `.any` returns true if *any* element
      -- satisfies the predicate.
      -- `.isSome` on `Option T` is true when the value is `some _`.
      !(allPositions n).any fun (r, c) =>
        r == sr && between sc tc c && (b (r, c)).isSome
    else if sc == tc then
      -- Same column: the rook slides vertically.
      !(allPositions n).any fun (r, c) =>
        c == sc && between sr tr r && (b (r, c)).isSome
    else
      -- Different row AND different column — rooks can't attack diagonally.
      false


-- ------------------------------------------------------------
-- WITHIN-ONE HELPER
-- ------------------------------------------------------------
-- True when |a - b| ≤ 1. Written symmetrically using `max`/`min` so that
-- `withinOne a b = withinOne b a` follows directly from `Nat.max_comm` and
-- `Nat.min_comm`. Equivalent to `a == b || a + 1 == b || b + 1 == a`.
def withinOne (a b : Nat) : Bool :=
  let d := max a b - min a b
  d == 0 || d == 1


-- ------------------------------------------------------------
-- KING ATTACK CHECK
-- ------------------------------------------------------------
-- A king attacks all squares immediately adjacent to it — up to 8
-- squares, one step in any direction (including diagonals).
--
-- We check "within one step" on each axis independently using `withinOne`,
-- then combine. Defining the per-axis check symmetrically (via max/min)
-- makes `kingAttacks` provably symmetric.
def kingAttacks {n : Nat} (src tgt : Pos n) : Bool :=
  -- A king does not attack its own square.
  if src == tgt then false
  else
    let (sr, sc) := src
    let (tr, tc) := tgt
    withinOne sr.val tr.val && withinOne sc.val tc.val


-- ------------------------------------------------------------
-- FIND THE KING
-- ------------------------------------------------------------
-- Scans all squares and returns the position of the first King of
-- color `c` it finds, or `none` if there is no such king on the board.
--
-- `List.find?` returns `Option (Pos n)` — the `?` in the name is a Lean
-- convention meaning "this might fail / return nothing".
--
-- `some ⟨c, .King⟩` constructs an `Option Piece` value to compare against.
-- `⟨c, .King⟩` is anonymous constructor syntax: Lean infers that we want
-- a `Piece` because that's what `b p` returns inside `Option`.
def findKing {n : Nat} (b : Board n) (c : Color) : Option (Pos n) :=
  (allPositions n).find? fun p => b p == some ⟨c, .King⟩


-- ------------------------------------------------------------
-- IS THE KING IN CHECK?
-- ------------------------------------------------------------
-- The main function. Returns `true` if the king of color `c` is
-- currently attacked by any opponent piece.
--
-- Steps:
--   1. Find where the king is. If there is no king, return false.
--   2. Scan every square for an opponent piece.
--   3. For each opponent piece, ask whether it attacks the king's square.
def isCheck {n : Nat} (b : Board n) (c : Color) : Bool :=
  -- `match` is Lean's pattern-matching expression, like a switch
  -- statement but exhaustive — we must handle every case.
  match findKing b c with
  | none =>
    -- No king on the board (shouldn't happen in a valid game, but the
    -- function is still total — it handles every possible board).
    false
  | some kingPos =>
    -- `kingPos` is now the unwrapped `Pos n` value.
    -- `List.any` short-circuits: it returns `true` as soon as one
    -- element satisfies the predicate.
    (allPositions n).any fun p =>
      match b p with
      | none =>
        -- Empty square — skip it.
        false
      | some piece =>
        -- There is a piece here. Only opponent pieces can give check.
        if piece.color == c.opponent then
          match piece.kind with
          | .Rook => rookAttacks b p kingPos
          | .King => kingAttacks p kingPos
        else
          false


-- ------------------------------------------------------------
-- APPLY A MOVE
-- ------------------------------------------------------------
-- Relocates the piece at `src` to `dst`, removing whatever was at `dst`
-- (a capture). Every other square is unchanged.
def applyMove {n : Nat} (b : Board n) (src dst : Pos n) : Board n :=
  fun p => if p == dst then b src else if p == src then none else b p


-- ------------------------------------------------------------
-- MOVE TARGET GENERATION
-- ------------------------------------------------------------
-- For each piece type, compute the squares it can move to from `src`
-- on board `b` for color `c`.
-- These are purely geometric — we do NOT yet filter out moves that
-- leave the king in check; `isCheckmate` does that via `isCheck`.

-- King: any adjacent square not occupied by a friendly piece.
def kingMoveTargets {n : Nat} (b : Board n) (src : Pos n) (c : Color) : List (Pos n) :=
  (allPositions n).filter fun dst =>
    kingAttacks src dst &&
    match b dst with
    | some p => p.color != c
    | none   => true

-- Rook: any square on the same rank or file with a clear path, not
-- occupied by a friendly piece.
-- `rookAttacks b src dst` already encodes "same rank/file AND clear path",
-- so we only add the friendly-piece guard on the destination square.
def rookMoveTargets {n : Nat} (b : Board n) (src : Pos n) (c : Color) : List (Pos n) :=
  (allPositions n).filter fun dst =>
    rookAttacks b src dst &&
    match b dst with
    | some p => p.color != c
    | none   => true


-- ------------------------------------------------------------
-- IS THE KING IN CHECKMATE?
-- ------------------------------------------------------------
-- Returns `true` if the king of color `c` is in check AND every
-- possible move by every friendly piece leaves the king still in check.
--
-- Steps:
--   1. Confirm the king is in check (necessary condition).
--   2. For each friendly piece, generate its candidate target squares.
--   3. For each target, apply the move with `applyMove` and test with
--      `isCheck`. If any move resolves the check, return false.
def isCheckmate {n : Nat} (b : Board n) (c : Color) : Bool :=
  isCheck b c &&
  !(allPositions n).any fun src =>
    match b src with
    | none => false
    | some piece =>
      if piece.color != c then false
      else
        let targets := match piece.kind with
          | .King => kingMoveTargets b src c
          | .Rook => rookMoveTargets b src c
        targets.any fun dst =>
          !isCheck (applyMove b src dst) c


-- ------------------------------------------------------------
-- IS THE SETUP LEGAL?
-- ------------------------------------------------------------
-- A legal setup requires:
--   1. Exactly one White King on the board.
--   2. Exactly one Black King on the board.
--   3. The two kings are not adjacent (not touching).
--
-- `List.filter` keeps only positions satisfying the predicate.
-- The `match` on singleton lists enforces exactly-one-of-each.
-- `!kingAttacks wp bp` then verifies the kings do not touch.
def isLegalSetup {n : Nat} (b : Board n) : Bool :=
  let whites := (allPositions n).filter fun p => b p == some ⟨.White, .King⟩
  let blacks := (allPositions n).filter fun p => b p == some ⟨.Black, .King⟩
  match whites, blacks with
  | [wp], [bp] => !kingAttacks wp bp
  | _, _ => false
