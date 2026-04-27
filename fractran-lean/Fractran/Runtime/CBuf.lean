/-!
# Circular Buffer (runtime)

A bounded circular buffer backed by an `Array`, used by the cycle-detecting
FRACTRAN interpreter to track recent logic states. Supports O(1) insertion
(with eviction of the oldest element when full) and O(n) key-based search.

For the small buffer sizes used in practice (≤ 16), linear search is used
rather than maintaining a separate set structure.

## Implementation

The buffer uses a flat `Array` with a `cursor` index pointing to the most
recently inserted element. During the growth phase (`buf.size < cap`), new
elements are appended via `push`. Once full, new elements overwrite the
oldest entry at `(cursor + 1) % size` and advance the cursor.

`buf.size` implicitly tracks the current element count (grows to `cap`,
then stays constant), so no separate length field is needed.

## Logical view

`toList` returns elements in newest-first order: `toList[0]` is the most
recently inserted element. The key specification is:

  `(cb.insert x).toList = (x :: cb.toList).take cb.cap`

The specification lemmas live in `Fractran.CBuf` on the proof side. CBuf
happens to need no mathlib at all, so this split is purely organizational
— it keeps the structure consistent with the rest of `Fractran.Runtime.*`.
-/

/-- Circular buffer of capacity `cap`, backed by an `Array`.
    `cursor` is the index of the most recently inserted element.
    The buffer grows from empty up to `cap`, then overwrites the oldest. -/
structure CBuf (α : Type) where
  /-- Maximum number of elements. -/
  cap : Nat
  /-- Backing storage. Size grows from 0 to `cap`, then stays at `cap`. -/
  buf : Array α
  /-- Index of the most recently inserted element in `buf`. -/
  cursor : Nat
  /-- Capacity is positive. -/
  hCapPos : 0 < cap
  /-- Array never exceeds capacity. -/
  hBufSize : buf.size ≤ cap
  /-- Cursor is valid when the buffer is non-empty. -/
  hCursor : buf.size = 0 ∨ cursor < buf.size
  /-- During the growth phase, cursor points to the last array slot.
      This ensures `toList` returns elements in reverse-array order,
      which is needed for `toList_insert` to hold. -/
  hGrowInv : buf.size < cap → buf.size = 0 ∨ cursor = buf.size - 1

namespace CBuf

variable {α β : Type}

/-- Number of elements currently stored. -/
@[inline] def len (cb : CBuf α) : Nat := cb.buf.size

/-- Create an empty buffer with the given capacity. -/
def empty (cap : Nat) (h : 0 < cap) : CBuf α where
  cap := cap
  buf := #[]
  cursor := 0
  hCapPos := h
  hBufSize := by simp
  hCursor := Or.inl rfl
  hGrowInv := fun _ => Or.inl rfl

/-- Insert a new element. Appends if not yet full; overwrites the oldest if full. -/
def insert (cb : CBuf α) (x : α) : CBuf α :=
  if h : cb.buf.size < cb.cap then
    -- Growing phase: push to the end
    { cap := cb.cap
      buf := cb.buf.push x
      cursor := cb.buf.size
      hCapPos := cb.hCapPos
      hBufSize := by simp [Array.size_push]; omega
      hCursor := Or.inr (by simp [Array.size_push])
      hGrowInv := fun _ => Or.inr (by simp [Array.size_push]) }
  else
    -- Full: advance cursor (wrapping) and overwrite
    have hPos : 0 < cb.buf.size := by have := cb.hCapPos; omega
    let next := (cb.cursor + 1) % cb.buf.size
    have hNext : next < cb.buf.size := Nat.mod_lt _ hPos
    { cap := cb.cap
      buf := cb.buf.set next x hNext
      cursor := next
      hCapPos := cb.hCapPos
      hBufSize := by simp only [Array.size_set]; exact cb.hBufSize
      hCursor := Or.inr (by simp only [Array.size_set]; exact hNext)
      hGrowInv := fun hlt => by simp only [Array.size_set] at hlt; omega }

/-- Logical view: elements in newest-first order.
    Element `0` is the most recently inserted; element `len - 1` is the oldest. -/
def toList (cb : CBuf α) : List α :=
  if h : cb.buf.size = 0 then []
  else
    have hPos : 0 < cb.buf.size := by omega
    List.ofFn fun (i : Fin cb.buf.size) =>
      cb.buf[(cb.cursor + cb.buf.size - i.val) % cb.buf.size]'(Nat.mod_lt _ hPos)

/-- Search for an element whose key matches `key`. If found, return the prefix
    of `toList` from the newest element through the match (inclusive).
    This prefix represents the detected cycle and is passed to `leap`. -/
def getRange [BEq β] (cb : CBuf α) (keyFn : α → β) (key : β) : Option (List α) :=
  let l := cb.toList
  l.findIdx? (fun x => keyFn x == key) |>.map (fun i => l.take (i + 1))

/-- Check if any element in the buffer has the given key. -/
def hasKey [BEq β] (cb : CBuf α) (keyFn : α → β) (key : β) : Bool :=
  cb.buf.any (fun x => keyFn x == key)

end CBuf
