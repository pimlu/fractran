import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

/-!
# Circular Buffer

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

/-! ## Specification lemmas -/

@[simp] theorem len_empty (cap : Nat) (h : 0 < cap) :
    (empty cap h : CBuf α).len = 0 := by
  simp [len, empty]

@[simp] theorem toList_empty (cap : Nat) (h : 0 < cap) :
    (empty cap h : CBuf α).toList = [] := by
  simp [toList, empty]

theorem toList_length (cb : CBuf α) : cb.toList.length = cb.len := by
  unfold toList len
  split
  · next h => simp [h]
  · exact List.length_ofFn

theorem len_insert (cb : CBuf α) (x : α) :
    (cb.insert x).len = min (cb.len + 1) cb.cap := by
  simp only [len, insert]
  split
  · next h => simp only [Array.size_push]; omega
  · next h =>
    have hle := cb.hBufSize
    simp only [Array.size_set]
    omega

theorem getElem_toList (cb : CBuf α) (i : Nat) (hi : i < cb.toList.length) :
    cb.toList[i] = cb.buf[(cb.cursor + cb.buf.size - i) % cb.buf.size]'(by
      apply Nat.mod_lt
      rw [toList_length, len] at hi; omega) := by
  unfold toList
  have hne : ¬cb.buf.size = 0 := by rw [toList_length, len] at hi; omega
  simp only [hne, ↓reduceDIte, List.getElem_ofFn]

/-- The key specification: inserting prepends to the logical view and
    truncates to capacity. -/
theorem toList_insert (cb : CBuf α) (x : α) :
    (cb.insert x).toList = (x :: cb.toList).take cb.cap := by
  by_cases hlt : cb.buf.size < cb.cap
  · -- Growing phase: insert pushes x, cursor' = buf.size, size' = buf.size + 1
    have hlen : (x :: cb.toList).length ≤ cb.cap := by
      rw [List.length_cons, toList_length, len]; omega
    rw [List.take_of_length_le hlen]
    -- Unfold insert then toList on LHS
    simp only [insert, hlt, ↓reduceDIte]
    unfold toList
    simp only [Array.size_push]
    have hne : ¬(cb.buf.size + 1 = 0) := by omega
    simp only [hne, ↓reduceDIte]
    -- LHS: ofFn (i : Fin (n+1)) => (buf.push x)[(n + (n+1) - i) % (n+1)]
    -- RHS: x :: (if n = 0 then [] else ofFn (i : Fin n) => buf[(c + n - i) % n])
    -- Use ext
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_cons]
      split
      · next h => simp [h]
      · simp [List.length_ofFn]
    · intro i hi1 hi2
      simp only [List.length_ofFn, Array.size_push] at hi1
      have hi1' := hi1  -- i < cb.buf.size + 1
      simp only [List.getElem_ofFn]
      by_cases hi0 : i = 0
      · subst hi0
        simp only [Nat.sub_zero, List.getElem_cons_zero,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : cb.buf.size < cb.buf.size + 1),
          Array.getElem_push_eq]
      · -- i > 0: both sides should give buf[n - i]
        have hi_pos : 0 < i := by omega
        have hi_le : i ≤ cb.buf.size := Nat.lt_succ_iff.mp hi1'
        have hne2 : ¬(cb.buf.size = 0) := by omega
        have hcur : cb.cursor = cb.buf.size - 1 := by
          cases cb.hGrowInv hlt with
          | inl h => omega
          | inr h => exact h
        -- Goal: (buf.push x)[lhs_idx] = (x :: if n=0 then [] else ofFn ...)[i]
        -- RHS: since i > 0 and n > 0, this is (ofFn ...)[i-1] = buf[rhs_idx]
        -- Use getElem_cons_succ to peel off x, then getElem_ofFn
        -- LHS: use getElem_push_lt to remove the push
        -- Both reduce to buf[n - i]
        have hlhs_idx : (cb.buf.size + (cb.buf.size + 1) - i) %
            (cb.buf.size + 1) = cb.buf.size - i := by
          rw [show cb.buf.size + (cb.buf.size + 1) - i =
            cb.buf.size - i + (cb.buf.size + 1) from by omega]
          rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
        have hlhs_lt : cb.buf.size - i < cb.buf.size := by omega
        -- RHS simplification: (x :: if false then [] else ofFn f)[i] = (ofFn f)[i-1]
        -- First eliminate the dite
        simp only [hne2, ↓reduceDIte]
        -- LHS: (buf.push x)[lhs_idx], reduce with getElem_push_lt
        have hlhs_bound : (cb.buf.size + (cb.buf.size + 1) - i) %
            (cb.buf.size + 1) < cb.buf.size := by
          rw [hlhs_idx]; exact hlhs_lt
        rw [Array.getElem_push_lt hlhs_bound]
        -- RHS: (x :: ofFn f)[i] where i > 0, use getElem_cons
        rw [List.getElem_cons]
        simp only [hi0, ↓reduceDIte, List.getElem_ofFn]
        -- Now: buf[lhs_idx] = buf[rhs_idx], use congr
        have hrhs_idx : (cb.cursor + cb.buf.size - (i - 1)) %
            cb.buf.size = cb.buf.size - i := by
          rw [hcur, show cb.buf.size - 1 + cb.buf.size - (i - 1) =
            cb.buf.size - i + cb.buf.size from by omega]
          rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
        congr 1
        exact hlhs_idx.trans hrhs_idx.symm
  · -- Full phase: buf.size = cap, next = (cursor+1) % n, buf' = buf.set next x
    have hfull : cb.buf.size = cb.cap := by have := cb.hBufSize; omega
    have hne : ¬cb.buf.size = 0 := by have := cb.hCapPos; omega
    have hPos : 0 < cb.buf.size := by omega
    -- RHS: (x :: toList).take cap. Length = cap since toList.length = cap.
    -- LHS: (insert x).toList. Length = cap since buf.set preserves size.
    apply List.ext_getElem
    · rw [toList_length, len_insert, List.length_take,
        List.length_cons, toList_length, len]; omega
    · intro i hi1 hi2
      rw [toList_length, len_insert] at hi1
      have hi_lt : i < cb.buf.size := by omega
      -- LHS: getElem_toList on insert x
      rw [getElem_toList]
      simp only [insert, hlt, ↓reduceDIte, Array.size_set]
      -- RHS: (x :: toList).take cap at index i
      rw [List.getElem_take]
      -- Now: buf.set next x at index ... = (x :: toList)[i]
      -- Use getElem_cons for RHS
      rw [List.getElem_cons]
      -- Split on i = 0
      by_cases hi0 : i = 0
      · -- i = 0: newest element is x
        subst hi0
        simp only [↓reduceDIte, Nat.sub_zero]
        -- LHS: (buf.set next x)[(next + n - 0) % n]
        -- = (buf.set next x)[next] = x
        rw [Array.getElem_set]
        -- Goal: if next = next % n then x else buf[next % n] = x
        -- next % n = next since next = (cursor+1) % n < n
        have hmod : (cb.cursor + 1) % cb.buf.size % cb.buf.size = (cb.cursor + 1) % cb.buf.size :=
          Nat.mod_eq_of_lt (Nat.mod_lt _ hPos)
        simp [hmod]
      · -- i > 0: LHS is buf.set at next, accessed at index ≠ next
        simp only [hi0, ↓reduceDIte]
        have hi_pos : 0 < i := by omega
        -- Expand RHS using getElem_toList
        rw [getElem_toList]
        -- LHS: (buf.set next x)[idx1], RHS: buf[idx2]
        -- idx1 = ((cursor+1)%n + n - i) % n
        -- idx2 = (cursor + n - (i-1)) % n
        -- These are equal: both = (cursor + n - i + 1) % n
        -- And idx1 ≠ next, so getElem_set gives buf[idx1]
        rw [Array.getElem_set]
        -- Goal: if next = idx then x else buf[idx] = buf[rhs_idx]
        -- where next = (cursor+1)%n, idx = (next + n - i) % n, rhs_idx = (cursor+n-(i-1))%n
        -- next ≠ idx for 0 < i < n
        have hc_lt := Nat.mod_lt (cb.cursor + 1) hPos
        -- Prove next ≠ idx
        -- Let c = (cursor+1)%n. We need c ≠ (c+n-i)%n for 0 < i < n.
        -- Case c ≥ i: (c+n-i)%n = c-i ≠ c
        -- Case c < i: (c+n-i)%n = c+n-i ≠ c (since n-i > 0)
        have hne_idx : ¬(cb.cursor + 1) % cb.buf.size =
            ((cb.cursor + 1) % cb.buf.size + cb.buf.size - i) % cb.buf.size := by
          intro heq
          by_cases hci : i ≤ (cb.cursor + 1) % cb.buf.size
          · have h1 : (cb.cursor + 1) % cb.buf.size + cb.buf.size - i ≥ cb.buf.size := by omega
            have h2 : (cb.cursor + 1) % cb.buf.size + cb.buf.size -
                i - cb.buf.size < cb.buf.size := by omega
            rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2] at heq; omega
          · have h1 : (cb.cursor + 1) % cb.buf.size + cb.buf.size - i < cb.buf.size := by omega
            rw [Nat.mod_eq_of_lt h1] at heq; omega
        rw [if_neg hne_idx]
        -- buf[idx1] = buf[idx2]
        -- Show indices are equal modulo
        congr 1
        -- ((cursor+1)%n + n - i) % n = (cursor + n - (i-1)) % n
        -- Rewrite both to use Nat.add_mod
        have hni : cb.buf.size - i < cb.buf.size := by omega
        rw [show (cb.cursor + 1) % cb.buf.size + cb.buf.size - i =
            (cb.cursor + 1) % cb.buf.size + (cb.buf.size - i) from by omega,
            show cb.cursor + cb.buf.size - (i - 1) =
            cb.cursor + 1 + (cb.buf.size - i) from by omega]
        rw [Nat.add_mod ((cb.cursor + 1) % cb.buf.size) (cb.buf.size - i),
            Nat.mod_mod, Nat.add_mod (cb.cursor + 1)]

/-- `getRange` returns `none` iff no element has the given key. -/
theorem getRange_none_iff [BEq β] [LawfulBEq β] (cb : CBuf α) (keyFn : α → β) (key : β) :
    cb.getRange keyFn key = none ↔ ∀ x ∈ cb.toList, keyFn x ≠ key := by
  simp only [getRange, Option.map_eq_none_iff]
  rw [List.findIdx?_eq_none_iff]
  constructor <;> intro h x hx <;> simpa using h x hx

/-- When `getRange` returns `some l`, `l` is a non-empty prefix of `toList`
    whose last element has the matching key. -/
theorem getRange_some_spec [BEq β] [LawfulBEq β] (cb : CBuf α) (keyFn : α → β) (key : β)
    (l : List α) (h : cb.getRange keyFn key = some l) (hne : l ≠ []) :
    l <+: cb.toList ∧ keyFn (l.getLast hne) = key := by
  simp only [getRange, Option.map_eq_some_iff] at h
  obtain ⟨idx, hfind, rfl⟩ := h
  rw [List.findIdx?_eq_some_iff_getElem] at hfind
  obtain ⟨hidx, hpidx, _⟩ := hfind
  constructor
  · exact List.take_prefix _ _
  · -- The last element of take (idx + 1) is toList[idx]
    have hlen : (cb.toList.take (idx + 1)).length = idx + 1 := by
      rw [List.length_take]; omega
    rw [List.getLast_eq_getElem]
    simp only [List.getElem_take, hlen]
    simpa using hpidx

end CBuf
