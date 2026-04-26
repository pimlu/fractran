import Fractran.Elim
import Fractran.CBuf
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cycle Detection with Arithmetic Leaping

The main optimization: partition registers into *data* (large exponents that
cannot affect control flow) and *logic* (small exponents that determine which
fraction fires). When the logic state repeats, compute how many full cycles
can safely be skipped before any data register drops into logic territory,
then advance the state arithmetically.

## Overview of the proof

The correctness proof has three layers:

1. **Data-register irrelevance** (`data_irrelevant`): if every register in a
   set `D` satisfies `m.get p ≥ dthresh p`, then changing those registers
   doesn't change which fraction fires. This is Lemma 1 in the paper.

2. **Cycle repetition** (`cycle_repeats`): if the logic state at step `i`
   equals the logic state at step `j` (with `i > j`), then the same sequence
   of fractions fires for `c` full cycles, where `c = min {life_p}`.
   This is Theorem 2 in the paper.

3. **Interpreter correctness** (`cycleRun_correct`): the cycle-detecting
   interpreter satisfies `Correct`, i.e. it agrees with `naiveRun` at the
   reported step count.

## Correspondence to Haskell implementation

- `dthresh`       ↔ `dthresh` in Fractran.hs (line 137)
- `stateSplit`    ↔ `stateSplit` in Fractran.hs (line 97-99)
- `leapCount`     ↔ `leap` in Fractran.hs (line 101-128), the `steps` part
- `leapState`     ↔ `leap` in Fractran.hs, the `n` part
- `cycleRunNat`   ↔ `cycles'` in Fractran.hs (line 133-151)
-/

/-! ## Threshold and state splitting -/

/-- Maximum exponent of prime `p` across all denominators in the program.
    Corresponds to `m_p = max_{i} b_{i,p}` in the paper. -/
def maxDenom (prog : List (RegMap × RegMap)) (p : ℕ) : ℕ :=
  prog.foldl (fun acc (_, den) => max acc (den.getD p 0)) 0

/-- The threshold for prime `p` above which a register is considered "data".
    A register with exponent `≥ dthresh` cannot affect which fraction fires.
    Corresponds to `l · m_p` in the paper, where `l` is the cycle buffer
    capacity (here we use the cycle length from the buffer). -/
def dthresh (prog : List (RegMap × RegMap)) (cyclen : ℕ) (p : ℕ) : ℕ :=
  cyclen * maxDenom prog p

/-- The threshold as a RegMap: maps each prime appearing in any denominator
    to its `dthresh` value. Corresponds to `dthresh` in Fractran.hs. -/
def dthreshMap (prog : List (RegMap × RegMap)) (cyclen : ℕ) : RegMap :=
  let allDenPrimes := prog.foldl (fun acc (_, den) =>
    den.foldl (fun a p _ => a.insert p 0) acc) (∅ : RegMap)
  allDenPrimes.foldl (fun acc p _ =>
    let v := dthresh prog cyclen p
    if v = 0 then acc else acc.insert p v) ∅

/-- Split a state into (data, logic) components relative to a threshold map.
    - **data**: registers with exponent `> thresh_p` — the excess above threshold
    - **logic**: registers with exponent `≤ thresh_p` — `min(exp, thresh)` per prime

    The original state can be recovered as `data * logic` (pointwise exponent
    addition), since for each prime: `(exp - min(exp, thresh)) + min(exp, thresh) = exp`.

    In the Haskell: `stateSplit :: IntMap -> IntMap -> (IntMap, IntMap)`.
    There, data registers are those where `a >= thresh`, putting the excess in data
    and `thresh` in logic. We follow the same convention.

    Note: primes not in `thresh` (no denominator mentions them) are placed entirely
    in data, since they can never affect fraction applicability. -/
def stateSplit (thresh : RegMap) (m : RegMap) : RegMap × RegMap :=
  let logic := m.foldl (fun acc p e =>
    let t := thresh.getD p 0
    if t = 0 then acc
    else
      let logicVal := min e t
      if logicVal = 0 then acc else acc.insert p logicVal) ∅
  let data := m.foldl (fun acc p e =>
    let t := thresh.getD p 0
    let dataVal := if t = 0 then e else e - min e t
    if dataVal = 0 then acc else acc.insert p dataVal) ∅
  (data, logic)

/-- Helper: conditional foldl when key not present returns init. -/
private theorem foldl_cond_none (l : List (ℕ × ℕ)) (g : ℕ → ℕ → ℕ) (p : ℕ) (init : ℕ)
    (h : p ∉ l.map Prod.fst) :
    l.foldl (fun acc (x : ℕ × ℕ) => if x.1 = p then g x.1 x.2 else acc) init = init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons, show hd.1 ≠ p from fun h' => h.1 h'.symm, ite_false]
    exact ih _ h.2

/-- Helper: foldl that conditionally inserts into a map.
    Generalized to arbitrary accumulator. If `p` doesn't appear in `l`,
    the result `getD p 0` equals the accumulator's value. If `p` appears
    exactly once (guaranteed by nodup), the result is `g(p, e)` (or the
    accumulator value if `g` returns 0). -/
private theorem foldl_cond_insert_getD_gen (l : List (ℕ × ℕ)) (g : ℕ → ℕ → ℕ)
    (p : ℕ) (acc : RegMap)
    (hnodup : (l.map Prod.fst).Nodup)
    (hp_notin : p ∉ l.map Prod.fst) :
    (l.foldl (fun acc' (x : ℕ × ℕ) =>
      let v := g x.1 x.2; if v = 0 then acc' else acc'.insert x.1 v)
      acc).getD p 0 = acc.getD p 0 := by
  induction l generalizing acc with
  | nil => rfl
  | cons hd rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or, List.nodup_cons] at hp_notin hnodup
    simp only [List.foldl_cons]
    by_cases hv : g hd.1 hd.2 = 0
    · simp only [hv, ↓reduceIte]
      exact ih acc hnodup.2 hp_notin.2
    · simp only [hv, ↓reduceIte]
      rw [ih _ hnodup.2 hp_notin.2]
      rw [Std.TreeMap.getD_insert]
      simp only [compare_eq_iff_eq, show hd.1 ≠ p from fun h => hp_notin.1 h.symm, ite_false]

/-- Data fold of `stateSplit`: if `p` is not a key in `l`, result `getD p` = acc's. -/
private theorem data_foldl_getD_gen (l : List (ℕ × ℕ)) (thresh : RegMap)
    (p : ℕ) (acc : RegMap)
    (hnodup : (l.map Prod.fst).Nodup) (hp : p ∉ l.map Prod.fst) :
    (l.foldl (fun acc' (x : ℕ × ℕ) =>
        if (if thresh.getD x.1 0 = 0 then x.2 else x.2 - min x.2 (thresh.getD x.1 0)) = 0
        then acc'
        else acc'.insert x.1
          (if thresh.getD x.1 0 = 0 then x.2
           else x.2 - min x.2 (thresh.getD x.1 0)))
      acc).getD p 0 =
    acc.getD p 0 := by
  exact foldl_cond_insert_getD_gen l
    (fun q e => if thresh.getD q 0 = 0 then e else e - min e (thresh.getD q 0)) p acc hnodup hp

/-- Logic fold of `stateSplit`: if `p` is not a key in `l`, result `getD p` = acc's. -/
private theorem logic_foldl_getD_gen (l : List (ℕ × ℕ)) (thresh : RegMap)
    (p : ℕ) (acc : RegMap)
    (hnodup : (l.map Prod.fst).Nodup) (hp : p ∉ l.map Prod.fst) :
    (l.foldl (fun acc' (x : ℕ × ℕ) =>
        if thresh.getD x.1 0 = 0 then acc'
        else if min x.2 (thresh.getD x.1 0) = 0 then acc'
             else acc'.insert x.1 (min x.2 (thresh.getD x.1 0))) acc).getD p 0 =
    acc.getD p 0 := by
  induction l generalizing acc with
  | nil => rfl
  | cons hd rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or, List.nodup_cons] at hnodup hp
    simp only [List.foldl_cons]
    have hne : hd.1 ≠ p := fun h => hp.1 h.symm
    -- The step at hd doesn't affect key p since hd.1 ≠ p
    -- After the step, the accumulator may or may not have changed
    -- but getD p is unchanged regardless
    -- ih gives: (rest.foldl f stepped_acc).getD p 0 = stepped_acc.getD p 0
    -- We need: ... = acc.getD p 0
    -- So: stepped_acc.getD p 0 = acc.getD p 0 (since hd.1 ≠ p)
    set stepped := (if thresh.getD hd.1 0 = 0 then acc
      else if min hd.2 (thresh.getD hd.1 0) = 0 then acc
           else acc.insert hd.1 (min hd.2 (thresh.getD hd.1 0)))
    have hstep : stepped.getD p 0 = acc.getD p 0 := by
      simp only [stepped]
      by_cases ht : thresh.getD hd.1 0 = 0
      · simp [ht]
      · simp only [ht, ↓reduceIte]
        by_cases hmin : min hd.2 (thresh.getD hd.1 0) = 0
        · simp [hmin]
        · simp only [hmin, ↓reduceIte]
          simp [Std.TreeMap.getD_insert, hne]
    rw [ih stepped hnodup.2 hp.2, hstep]

/-- The state can be recovered from its split: for every prime, the exponents
    in `data * logic` agree with `m`. -/
theorem stateSplit_recover (thresh m : RegMap) (p : ℕ) :
    let (data, logic) := stateSplit thresh m
    (data * logic).getD p 0 = m.getD p 0 := by
  simp only [stateSplit]
  rw [RegMap.mul_getD]
  -- Convert TreeMap.foldl to List.foldl
  rw [Std.TreeMap.foldl_eq_foldl_toList, Std.TreeMap.foldl_eq_foldl_toList]
  set l := m.toList
  have hnodup : (l.map Prod.fst).Nodup := by
    simp only [l, Std.TreeMap.map_fst_toList_eq_keys]; exact Std.TreeMap.nodup_keys
  by_cases hp : p ∈ m
  · -- p ∈ m: split l around the entry for p
    have hget := Std.TreeMap.getElem?_eq_some_getD_of_contains
                   ((Std.TreeMap.contains_iff_mem).mpr hp) (fallback := 0)
    have hmem := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mpr hget
    obtain ⟨l₁, l₂, hlist⟩ := List.mem_iff_append.mp hmem
    -- hlist : m.toList = l₁ ++ ... but hnodup mentions l = m.toList
    have hlist' : l = l₁ ++ (p, m.getD p 0) :: l₂ := hlist
    -- Extract nodup properties
    rw [hlist', List.map_append, List.map_cons] at hnodup
    rw [List.nodup_append] at hnodup
    obtain ⟨hnd1, hnd_r, hdisj⟩ := hnodup
    have hp1 : p ∉ l₁.map Prod.fst := by
      intro h; exact absurd rfl (hdisj _ h p (List.mem_cons_self ..))
    have hp2 : p ∉ l₂.map Prod.fst := (List.nodup_cons.mp hnd_r).1
    have hnd2 : (l₂.map Prod.fst).Nodup := (List.nodup_cons.mp hnd_r).2
    -- Split foldl at the entry for p
    rw [show l = l₁ ++ (p, m.getD p 0) :: l₂ from hlist',
        List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
    -- After l₁: both getD p = ∅.getD p = 0 (p ∉ l₁)
    -- After (p, e): data getD p = data_val, logic getD p = logic_val
    -- After l₂: both preserved (p ∉ l₂)
    set e := m.getD p 0
    -- Use gen lemmas to handle l₂
    -- After l₂: gen lemmas show getD p is preserved
    -- Goal should be about the values after processing l₁ and the (p, e) step
    -- Let me first handle l₁ with gen lemmas, then the (p, e) step directly
    -- l₂ doesn't touch p
    rw [data_foldl_getD_gen l₂ thresh p _ hnd2 hp2]
    rw [logic_foldl_getD_gen l₂ thresh p _ hnd2 hp2]
    -- Handle the conditional insert at p
    -- Data: (if dv = 0 then acc else acc.insert p dv).getD p
    -- Logic: (if t = 0 then acc else if lv = 0 then acc else acc.insert p lv).getD p
    -- In both cases, acc = l₁.foldl ∅, and acc.getD p 0 = 0 (since p ∉ l₁)
    simp only []
    -- Split on whether data value is 0
    by_cases hd : (if thresh.getD p 0 = 0 then e else e - min e (thresh.getD p 0)) = 0
    · simp only [hd, ↓reduceIte]
      rw [data_foldl_getD_gen l₁ thresh p ∅ hnd1 hp1]
      simp only [Std.TreeMap.getD_emptyc]
      by_cases ht : thresh.getD p 0 = 0
      · simp only [ht, ↓reduceIte] at hd ⊢
        rw [logic_foldl_getD_gen l₁ thresh p ∅ hnd1 hp1]
        simp [Std.TreeMap.getD_emptyc, hd]
      · simp only [ht, ↓reduceIte] at hd ⊢
        by_cases hmin : min e (thresh.getD p 0) = 0
        · simp only [hmin, ↓reduceIte]
          rw [logic_foldl_getD_gen l₁ thresh p ∅ hnd1 hp1]
          simp [Std.TreeMap.getD_emptyc]; omega
        · simp only [hmin, ↓reduceIte]
          rw [Std.TreeMap.getD_insert, show compare p p = .eq from compare_eq_iff_eq.mpr rfl]
          simp only [ite_true]; omega
    · simp only [hd, ↓reduceIte]
      rw [Std.TreeMap.getD_insert, show compare p p = .eq from compare_eq_iff_eq.mpr rfl]
      simp only [ite_true]
      by_cases ht : thresh.getD p 0 = 0
      · simp only [ht, ↓reduceIte] at hd ⊢
        rw [logic_foldl_getD_gen l₁ thresh p ∅ hnd1 hp1]
        simp [Std.TreeMap.getD_emptyc]
      · simp only [ht, ↓reduceIte] at hd ⊢
        by_cases hmin : min e (thresh.getD p 0) = 0
        · simp only [hmin, ↓reduceIte]
          rw [logic_foldl_getD_gen l₁ thresh p ∅ hnd1 hp1]
          simp [Std.TreeMap.getD_emptyc]
        · simp only [hmin, ↓reduceIte]
          rw [Std.TreeMap.getD_insert, show compare p p = .eq from compare_eq_iff_eq.mpr rfl]
          simp only [ite_true]; omega
  · -- p ∉ m: both folds give 0
    rw [Std.TreeMap.getD_eq_fallback hp]
    have hp_l : p ∉ l.map Prod.fst := by
      rw [Std.TreeMap.map_fst_toList_eq_keys]
      exact fun hmem => hp (Std.TreeMap.mem_of_mem_keys hmem)
    rw [data_foldl_getD_gen l thresh p ∅ hnodup hp_l]
    rw [logic_foldl_getD_gen l thresh p ∅ hnodup hp_l]
    simp [Std.TreeMap.getD_emptyc]

/-- Characterization of the logic component of `stateSplit`:
    the logic register for prime `p` is `min(m.getD p, thresh.getD p)`,
    or `0` if the threshold is zero. -/
theorem stateSplit_logic_getD (thresh m : RegMap) (p : ℕ) :
    (stateSplit thresh m).2.getD p 0 =
    if thresh.getD p 0 = 0 then 0
    else min (m.getD p 0) (thresh.getD p 0) := by
  simp only [stateSplit]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  set l := m.toList
  have hnodup : (l.map Prod.fst).Nodup := by
    simp only [l, Std.TreeMap.map_fst_toList_eq_keys]; exact Std.TreeMap.nodup_keys
  by_cases hp : p ∈ m
  · have hget := Std.TreeMap.getElem?_eq_some_getD_of_contains
                   ((Std.TreeMap.contains_iff_mem).mpr hp) (fallback := 0)
    have hmem := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mpr hget
    obtain ⟨l₁, l₂, hlist⟩ := List.mem_iff_append.mp hmem
    have hlist' : l = l₁ ++ (p, m.getD p 0) :: l₂ := hlist
    rw [hlist', List.map_append, List.map_cons] at hnodup
    rw [List.nodup_append] at hnodup
    obtain ⟨hnd1, hnd_r, hdisj⟩ := hnodup
    have hp1 : p ∉ l₁.map Prod.fst := by
      intro h; exact absurd rfl (hdisj _ h p (List.mem_cons_self ..))
    have hp2 : p ∉ l₂.map Prod.fst := (List.nodup_cons.mp hnd_r).1
    have hnd2 : (l₂.map Prod.fst).Nodup := (List.nodup_cons.mp hnd_r).2
    rw [hlist', List.foldl_append, List.foldl_cons]
    set e := m.getD p 0
    rw [logic_foldl_getD_gen l₂ thresh p _ hnd2 hp2]
    by_cases ht : thresh.getD p 0 = 0
    · simp only [ht, ↓reduceIte]
      rw [logic_foldl_getD_gen l₁ thresh p ∅ hnd1 hp1]
      simp [Std.TreeMap.getD_emptyc]
    · simp only [ht, ↓reduceIte]
      by_cases hmin : min e (thresh.getD p 0) = 0
      · simp only [hmin, ↓reduceIte]
        rw [logic_foldl_getD_gen l₁ thresh p ∅ hnd1 hp1]
        simp [Std.TreeMap.getD_emptyc]
      · simp only [hmin, ↓reduceIte]
        rw [Std.TreeMap.getD_insert, show compare p p = .eq from compare_eq_iff_eq.mpr rfl]
        simp only [ite_true]
  · rw [Std.TreeMap.getD_eq_fallback hp]
    have hp_l : p ∉ l.map Prod.fst := by
      rw [Std.TreeMap.map_fst_toList_eq_keys]
      exact fun hmem => hp (Std.TreeMap.mem_of_mem_keys hmem)
    rw [logic_foldl_getD_gen l thresh p ∅ hnodup hp_l]
    simp [Std.TreeMap.getD_emptyc]

/-- Characterization of the data component of `stateSplit`. Derived from
    `stateSplit_logic_getD` and `stateSplit_recover`. -/
theorem stateSplit_data_getD (thresh m : RegMap) (p : ℕ) :
    (stateSplit thresh m).1.getD p 0 =
    if thresh.getD p 0 = 0 then m.getD p 0
    else m.getD p 0 - min (m.getD p 0) (thresh.getD p 0) := by
  have hlogic := stateSplit_logic_getD thresh m p
  -- From stateSplit_recover: data.getD p + logic.getD p = m.getD p
  have hrec : (stateSplit thresh m).1.getD p 0 +
              (stateSplit thresh m).2.getD p 0 = m.getD p 0 := by
    have h := stateSplit_recover thresh m p
    simp only [] at h
    rwa [RegMap.mul_getD] at h
  by_cases ht : thresh.getD p 0 = 0
  · simp only [ht, ↓reduceIte] at hlogic ⊢; omega
  · simp only [ht, ↓reduceIte] at hlogic ⊢; omega

/-! ## Cycle metrics -/

/-- The margin for register `p` during a cycle: the minimum value reached
    during the cycle minus the threshold. If negative, the register dipped
    into logic territory during the cycle.

    `history` is the sequence of states from `n_j` through `n_i` (the cycle).
    Corresponds to `margin_p` in the paper. -/
def margin (thresh : RegMap) (history : List RegMap) (p : ℕ) : Int :=
  let minVal := history.foldl (fun acc m => min acc (m.getD p 0)) (history.head!.getD p 0)
  (minVal : Int) - (thresh.getD p 0 : Int)

/-- The "life" of register `p`: how many cycles it can sustain before
    potentially becoming a logic register.

    Returns `none` for infinite life (register is constant or increasing).
    Returns `some 0` if the margin is negative (already dipped).
    Returns `some k` for finite life.

    Corresponds to `life_p` in the paper and `life` in `leap` (Fractran.hs). -/
def life (thresh : RegMap) (history : List RegMap) (startState endState : RegMap)
    (p : ℕ) : Option ℕ :=
  let s := startState.getD p 0 -- n_{j,p}
  let e := endState.getD p 0 -- n_{i,p}
  if s = e then none -- constant → infinite life
  else
    let m := margin thresh history p
    if m < 0 then some 0 -- already dipped into logic
    else if e > s then none -- increasing → infinite life
    else -- decreasing: life = margin / (s - e)
      some (m.toNat / (s - e))

/-- The number of safe cycle repetitions: minimum life across all data registers.
    Returns `none` if the cycle is nonterminating (all lives are infinite).

    Corresponds to `c = min {life_p | p ∈ D_i} ∪ {∞}` in the paper,
    and the `cs`/`steps` computation in `leap` (Fractran.hs lines 115-126). -/
def leapCount (thresh : RegMap) (history : List RegMap)
    (startData endData : RegMap) : Option ℕ :=
  let keys := (startData.foldl (fun acc p _ => acc.insert p 0) endData).toList.map Prod.fst
  let lives := keys.filterMap fun p => life thresh history
    (startData.foldl (fun acc k v => acc.insert k v) ∅)
    (endData.foldl (fun acc k v => acc.insert k v) ∅) p
  match lives with
  | [] => none -- all infinite → nonterminating cycle
  | l => some (l.foldl min l.head!)

/-- foldl insert preserves getD when the key is not in the list. -/
private theorem foldl_insert_getD_of_not_mem (l : List (ℕ × ℕ)) (p : ℕ) (acc : RegMap)
    (hp : p ∉ l.map Prod.fst) :
    (l.foldl (fun acc' (x : ℕ × ℕ) => acc'.insert x.1 x.2) acc).getD p 0 = acc.getD p 0 := by
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    simp only [List.foldl_cons]
    rw [ih (acc.insert hd.1 hd.2) hp.2]
    rw [Std.TreeMap.getD_insert]
    have hne : compare hd.1 p ≠ .eq := fun h => hp.1 (compare_eq_iff_eq.mp h).symm
    simp [hne]

/-- foldl insert returns the value `v` for a key `p` paired with `v` in a nodup list. -/
private theorem foldl_insert_getD_of_mem (l : List (ℕ × ℕ)) (p v : ℕ) (acc : RegMap)
    (hnodup : (l.map Prod.fst).Nodup) (hmem : (p, v) ∈ l) :
    (l.foldl (fun acc' (x : ℕ × ℕ) => acc'.insert x.1 x.2) acc).getD p 0 = v := by
  obtain ⟨l₁, l₂, hlist⟩ := List.mem_iff_append.mp hmem
  rw [hlist] at hnodup
  rw [List.map_append, List.map_cons, List.nodup_append] at hnodup
  obtain ⟨_, hnd_r, _⟩ := hnodup
  have hp2 : p ∉ l₂.map Prod.fst := (List.nodup_cons.mp hnd_r).1
  rw [hlist, List.foldl_append, List.foldl_cons]
  rw [foldl_insert_getD_of_not_mem l₂ p _ hp2]
  rw [Std.TreeMap.getD_insert, show compare p p = .eq from compare_eq_iff_eq.mpr rfl]
  rfl

/-- The "copy" foldl on TreeMap (insert each entry into ∅) preserves getD. -/
private theorem foldl_insert_copy_getD (m : RegMap) (p : ℕ) :
    (m.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)).getD p 0 = m.getD p 0 := by
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  set l := m.toList
  have hnodup : (l.map Prod.fst).Nodup := by
    simp only [l, Std.TreeMap.map_fst_toList_eq_keys]
    exact Std.TreeMap.nodup_keys
  by_cases hp : p ∈ m
  · have hget := Std.TreeMap.getElem?_eq_some_getD_of_contains
                   ((Std.TreeMap.contains_iff_mem).mpr hp) (fallback := 0)
    have hmem := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mpr hget
    exact foldl_insert_getD_of_mem l p _ ∅ hnodup hmem
  · rw [Std.TreeMap.getD_eq_fallback hp]
    have hp_l : p ∉ l.map Prod.fst := by
      rw [Std.TreeMap.map_fst_toList_eq_keys]
      exact fun hmem => hp (Std.TreeMap.mem_of_mem_keys hmem)
    rw [foldl_insert_getD_of_not_mem l p ∅ hp_l]
    simp [Std.TreeMap.getD_emptyc]

/-- foldl min ≤ initial value. -/
private theorem foldl_min_le_init (l : List ℕ) (init : ℕ) :
    l.foldl min init ≤ init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h1 := ih (min init hd)
    have h2 : min init hd ≤ init := min_le_left _ _
    omega

/-- foldl with `min acc (f x)` is ≤ initial value. -/
private theorem foldl_min_proj_le_init {α : Type*} (l : List α) (f : α → ℕ) (init : ℕ) :
    l.foldl (fun acc x => min acc (f x)) init ≤ init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h1 := ih (min init (f hd))
    have h2 : min init (f hd) ≤ init := min_le_left _ _
    omega

/-- foldl min ≤ any element of the list. -/
private theorem foldl_min_le_mem (l : List ℕ) (init : ℕ) (x : ℕ) (hx : x ∈ l) :
    l.foldl min init ≤ x := by
  induction l generalizing init with
  | nil => exact absurd hx List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with hxhd | h
    · rw [hxhd]
      have h1 := foldl_min_le_init tl (min init hd)
      have h2 : min init hd ≤ hd := min_le_right _ _
      omega
    · exact ih (min init hd) h

/-- foldl with `min acc (f x)` is ≤ `f x` for any `x` in the list. -/
private theorem foldl_min_proj_le_mem {α : Type*} (l : List α) (f : α → ℕ) (init : ℕ)
    (x : α) (hx : x ∈ l) :
    l.foldl (fun acc x => min acc (f x)) init ≤ f x := by
  induction l generalizing init with
  | nil => exact absurd hx List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with hxhd | h
    · rw [hxhd]
      have h1 := foldl_min_proj_le_init tl f (min init (f hd))
      have h2 : min init (f hd) ≤ f hd := min_le_right _ _
      omega
    · exact ih (min init (f hd)) h

/-- **leapCount safety spec.** When `leapCount` returns `some c` with `c > 0`,
    each register's data parts satisfy bounds derived from the per-register
    `life` computation:
    - For non-constant registers (`s ≠ e`), the margin is non-negative
      (`minVal ≥ thresh`), since otherwise `life` would be `some 0`, making `c = 0`.
    - For decreasing registers (`s > e`), the cycle bound holds:
      `c * (s - e) ≤ minVal - thresh`, derived from `c ≤ life = margin / (s - e)`.

    These bounds plus `minVal ≤ e` (since `e` is in the history) are what
    `leap_correct` needs to derive its safety condition for `iterated_cycle_per_reg`. -/
theorem leapCount_pos_imp (thresh : RegMap) (history : List RegMap)
    (startData endData : RegMap) (c : ℕ) (hc_pos : 0 < c)
    (hlc : leapCount thresh history startData endData = some c)
    (p : ℕ)
    (hp_in : p ∈ (startData.foldl (fun acc q _ => acc.insert q 0) endData).toList.map Prod.fst) :
    let s := startData.getD p 0
    let e := endData.getD p 0
    let minVal := history.foldl (fun acc m => min acc (m.getD p 0))
                    (history.head!.getD p 0)
    (s ≠ e → minVal ≥ thresh.getD p 0) ∧
    (s > e → c * (s - e) ≤ minVal - thresh.getD p 0) := by
  -- Get equalities for the foldl-copies
  have hsd_eq :
      (startData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)).getD p 0 =
        startData.getD p 0 :=
    foldl_insert_copy_getD startData p
  have hed_eq :
      (endData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)).getD p 0 =
        endData.getD p 0 :=
    foldl_insert_copy_getD endData p
  -- Compute life for our p in terms of original startData, endData getD values
  have hlife_p : life thresh history
      (startData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap))
      (endData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)) p =
      (if startData.getD p 0 = endData.getD p 0 then none
       else if margin thresh history p < 0 then some 0
       else if endData.getD p 0 > startData.getD p 0 then none
       else some ((margin thresh history p).toNat /
                  (startData.getD p 0 - endData.getD p 0))) := by
    unfold life
    simp only [hsd_eq, hed_eq]
  -- Bring leapCount into the form (match (filterMap ...) with [] => none | l => some _) = some c
  set keys := ((startData.foldl (fun acc q _ => acc.insert q 0) endData).toList.map Prod.fst)
    with hkeys_def
  change (match (keys.filterMap
            (fun q => life thresh history
              (startData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap))
              (endData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)) q)) with
          | [] => none
          | l => some (l.foldl min l.head!)) = some c at hlc
  -- Generalize the filterMap result to a list `lives`
  generalize hlives_def : (((startData.foldl (fun acc q _ => acc.insert q 0) endData).toList.map
        Prod.fst).filterMap (fun q => life thresh history
          (startData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap))
          (endData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)) q)) = lives at hlc
  -- Lives is non-empty (else hlc says some c = none)
  cases hlcs : lives with
  | nil => rw [hlcs] at hlc; simp at hlc
  | cons hd tl =>
    rw [hlcs] at hlc
    simp only [List.head!_cons, Option.some.injEq] at hlc
    -- hlc : (hd :: tl).foldl min hd = c
    have hall_ge : ∀ x ∈ hd :: tl, c ≤ x := by
      intro x hx
      have := foldl_min_le_mem (hd :: tl) hd x hx
      omega
    -- Helper: if life = some k at p, then k ∈ lives, hence c ≤ k
    have hlife_in_lives : ∀ k, life thresh history
        (startData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap))
        (endData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)) p = some k → k ∈ lives := by
      intro k hk
      rw [← hlives_def]
      exact List.mem_filterMap.mpr ⟨p, hp_in, hk⟩
    refine ⟨?_, ?_⟩
    · -- s ≠ e → minVal ≥ thresh
      intro hne
      by_contra hlt
      push Not at hlt
      have hmargin_neg : margin thresh history p < 0 := by
        unfold margin
        push_cast
        omega
      have hlife_zero : life thresh history
          (startData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap))
          (endData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)) p = some 0 := by
        rw [hlife_p, if_neg hne, if_pos hmargin_neg]
      have h0_in : 0 ∈ lives := hlife_in_lives 0 hlife_zero
      rw [hlcs] at h0_in
      have := hall_ge 0 h0_in
      omega
    · -- s > e → c * (s - e) ≤ minVal - thresh
      intro hgt
      have hne : startData.getD p 0 ≠ endData.getD p 0 := Nat.ne_of_gt hgt
      have hnotgt : ¬ (endData.getD p 0 > startData.getD p 0) := Nat.not_lt.mpr hgt.le
      have hmargin_nonneg : ¬ (margin thresh history p < 0) := by
        intro hmneg
        have hlife_zero : life thresh history
            (startData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap))
            (endData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)) p = some 0 := by
          rw [hlife_p, if_neg hne, if_pos hmneg]
        have h0_in : 0 ∈ lives := hlife_in_lives 0 hlife_zero
        rw [hlcs] at h0_in
        have := hall_ge 0 h0_in
        omega
      set k := (margin thresh history p).toNat / (startData.getD p 0 - endData.getD p 0)
        with hk_def
      have hlife_some_k : life thresh history
          (startData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap))
          (endData.foldl (fun acc k v => acc.insert k v) (∅ : RegMap)) p = some k := by
        rw [hlife_p, if_neg hne, if_neg hmargin_nonneg, if_neg hnotgt]
      have hk_in : k ∈ lives := hlife_in_lives k hlife_some_k
      rw [hlcs] at hk_in
      have hck : c ≤ k := hall_ge k hk_in
      have hsubpos : 0 < startData.getD p 0 - endData.getD p 0 := by omega
      have hcsub_le : c * (startData.getD p 0 - endData.getD p 0) ≤
                      (margin thresh history p).toNat := by
        rw [hk_def] at hck
        exact (Nat.le_div_iff_mul_le hsubpos).mp hck
      -- margin = (minVal : Int) - (thresh : Int), and margin ≥ 0,
      -- so margin.toNat = minVal - thresh in Nat (with truncated subtraction).
      have hmargin_def : margin thresh history p =
          ((history.foldl (fun acc m => min acc (m.getD p 0))
                          (history.head!.getD p 0) : Nat) : Int) -
          ((thresh.getD p 0 : Nat) : Int) := rfl
      rw [hmargin_def] at hmargin_nonneg hcsub_le
      omega

/-- Advance the state by `c` cycles. The new data registers are:
      data_new = endData + c * (endData - startData)
    (pointwise, where subtraction is on integers then clamped to ℕ).
    The logic registers stay the same.

    Corresponds to `n = fprod slogic newdata` in `leap` (Fractran.hs line 128)
    and `n_{i + c(i-j)} = n_i · (n_i / n_j)^c` in the paper. -/
def leapState (startData endData logic : RegMap) (c : ℕ) : RegMap :=
  let keys := (startData.foldl (fun acc p _ => acc.insert p 0) endData).toList.map Prod.fst
  let newData := keys.foldl (fun acc p =>
    let sv := startData.getD p 0
    let ev := endData.getD p 0
    let nv := if ev ≥ sv
      then ev + c * (ev - sv)
      else ev - c * (sv - ev)
    if nv = 0 then acc else acc.insert p nv) (∅ : RegMap)
  newData * logic

/-! ## Data-register irrelevance (Lemma 1 from the paper) -/

section DataIrrelevance

/-- `List.all` respects predicates that agree on all list elements. -/
private theorem all_congr_mem {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons, h hd (List.mem_cons_self ..),
      ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

/-- For a single fraction, applicability depends only on registers in `den`. -/
theorem applicable_of_eq_on_den (den m₁ m₂ : RegMap)
    (h : ∀ p ∈ den, m₁.getD p 0 = m₂.getD p 0) :
    RegMap.applicable den m₁ = RegMap.applicable den m₂ := by
  simp only [RegMap.applicable_eq_toList_all]
  apply all_congr_mem
  intro ⟨p, e⟩ hmem
  have hp : p ∈ den :=
    Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hmem]; rfl)
  rw [h p hp]

/-- Auxiliary: `foldl max` is monotone in the initial accumulator. -/
private theorem foldl_max_mono (l : List (RegMap × RegMap)) (p : ℕ) (a b : ℕ)
    (hab : a ≤ b) :
    l.foldl (fun acc (_, den) => max acc (den.getD p 0)) a ≤
    l.foldl (fun acc (_, den) => max acc (den.getD p 0)) b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih; omega

/-- Auxiliary: `foldl max` is at least the initial accumulator. -/
private theorem le_foldl_max (l : List (RegMap × RegMap)) (p : ℕ) (a : ℕ) :
    a ≤ l.foldl (fun acc (_, den) => max acc (den.getD p 0)) a := by
  induction l generalizing a with
  | nil => exact le_refl _
  | cons hd tl ih => exact le_trans (le_max_left _ _) (ih _)

/-- Each denominator's exponent is bounded by `maxDenom`. -/
theorem maxDenom_ge (prog : List (RegMap × RegMap)) (num den : RegMap)
    (hmem : (num, den) ∈ prog) (p : ℕ) :
    den.getD p 0 ≤ maxDenom prog p := by
  unfold maxDenom
  induction prog with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact le_trans (le_max_right _ _) (le_foldl_max tl p _)
    · exact le_trans (ih hmem) (foldl_max_mono tl p _ _ (le_max_left _ _))

private theorem applicable_agree_of_maxDenom (prog : List (RegMap × RegMap))
    (num den : RegMap) (hmem : (num, den) ∈ prog)
    (m₁ m₂ : RegMap)
    (hlogic : ∀ p, m₁.getD p 0 < maxDenom prog p → m₁.getD p 0 = m₂.getD p 0)
    (hdata : ∀ p, m₁.getD p 0 ≥ maxDenom prog p → m₂.getD p 0 ≥ maxDenom prog p) :
    RegMap.applicable den m₁ = RegMap.applicable den m₂ := by
  simp only [RegMap.applicable_eq_toList_all]
  apply all_congr_mem
  intro ⟨p, e⟩ hmem_tl
  have hp_den : p ∈ den :=
    Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hmem_tl]; rfl)
  have he : den.getD p 0 = e := RegMap.getD_of_mem_toList den hmem_tl
  have hle : e ≤ maxDenom prog p := he ▸ maxDenom_ge prog num den hmem p
  by_cases hlt : m₁.getD p 0 < maxDenom prog p
  · rw [hlogic p hlt]
  · simp only [not_lt] at hlt
    have h₁ : m₁.getD p 0 ≥ e := le_trans hle hlt
    have h₂ : m₂.getD p 0 ≥ e := le_trans hle (hdata p hlt)
    simp [decide_eq_true_eq.mpr h₁, decide_eq_true_eq.mpr h₂]

/-- **Lemma (Data-register irrelevance).**
    If two states agree on all "logic" registers (exponent below `maxDenom`)
    and both have data registers above the threshold, then `elimStep` picks
    the same fraction index on both.

    This is Lemma 1 in the paper. Requires candidates come from `prog`. -/
theorem data_irrelevant (prog : List (RegMap × RegMap))
    (candidates : List Candidate) (m₁ m₂ : RegMap)
    (hcands : ∀ c ∈ candidates, c.1 ∈ prog)
    (hlogic : ∀ p, m₁.getD p 0 < maxDenom prog p → m₁.getD p 0 = m₂.getD p 0)
    (hdata : ∀ p, m₁.getD p 0 ≥ maxDenom prog p → m₂.getD p 0 ≥ maxDenom prog p) :
    (elimStep candidates m₁).map Prod.fst =
    (elimStep candidates m₂).map Prod.fst := by
  simp only [elimStep]
  induction candidates with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨⟨num, den⟩, idx⟩ := c
    simp only [List.findSome?_cons]
    have hmem : (num, den) ∈ prog := hcands _ (List.mem_cons_self ..)
    have happ := applicable_agree_of_maxDenom prog num den hmem m₁ m₂ hlogic hdata
    cases happ₁ : RegMap.applicable den m₁
    · rw [happ] at happ₁
      simp only [happ₁]
      exact ih (fun c hc => hcands c (List.mem_cons.mpr (Or.inr hc)))
    · rw [happ] at happ₁
      simp [happ₁]

/-- After applying the same fraction, if both inputs agree on register `p`,
    the outputs agree on register `p`. This is the easy case that handles
    logic registers (which agree by hypothesis). -/
theorem applyFrac_getD_eq (num den m₁ m₂ : RegMap) (p : ℕ)
    (h : m₁.getD p 0 = m₂.getD p 0) :
    (num.applyFrac den m₁).getD p 0 = (num.applyFrac den m₂).getD p 0 := by
  simp only [RegMap.applyFrac, RegMap.mul_getD, RegMap.div_getD, h]

/-- After applying a fraction from `prog`, if the input had register `p ≥ maxDenom`,
    and the result drops below `maxDenom`, then the result is fully determined by
    `den.getD p 0` and `num.getD p 0` (it equals `m.getD p 0 - den.getD p 0 + num.getD p 0`
    but `m.getD p 0 - den.getD p 0` might be 0 due to saturation — actually since
    `m.getD p 0 ≥ maxDenom ≥ den.getD p 0`, there's no saturation). -/
theorem applyFrac_getD (num den m : RegMap) (p : ℕ) :
    (num.applyFrac den m).getD p 0 =
    m.getD p 0 - den.getD p 0 + num.getD p 0 := by
  simp only [RegMap.applyFrac, RegMap.mul_getD, RegMap.div_getD]

/-- **Bridge lemma**: if two states have matching logic components from
    `stateSplit` (with threshold ≥ maxDenom per prime), then they satisfy
    `data_irrelevant`'s preconditions. This connects the cycle detection's
    notion of "logic state match" to the fraction-level irrelevance lemma. -/
theorem logic_agree_implies_data_irrelevant
    (prog : List (RegMap × RegMap))
    (thresh : RegMap) (m₁ m₂ : RegMap)
    (hthresh : ∀ p, maxDenom prog p ≤ thresh.getD p 0)
    (hlogic : ∀ p, (stateSplit thresh m₁).2.getD p 0 =
                    (stateSplit thresh m₂).2.getD p 0) :
    (∀ p, m₁.getD p 0 < maxDenom prog p → m₁.getD p 0 = m₂.getD p 0) ∧
    (∀ p, m₁.getD p 0 ≥ maxDenom prog p → m₂.getD p 0 ≥ maxDenom prog p) := by
  constructor
  · -- Logic registers agree
    intro p hlt
    have htp := hthresh p
    have ht_ne : thresh.getD p 0 ≠ 0 := by omega
    have h₁ := stateSplit_logic_getD thresh m₁ p
    have h₂ := stateSplit_logic_getD thresh m₂ p
    simp only [ht_ne, ↓reduceIte] at h₁ h₂
    have heq := hlogic p
    rw [h₁, h₂] at heq
    simp only [Nat.min_def] at heq
    split_ifs at heq with h₃ h₄ <;> omega
  · -- Data registers both above maxDenom
    intro p hge
    have htp := hthresh p
    by_cases ht : thresh.getD p 0 = 0
    · omega
    · have h₁ := stateSplit_logic_getD thresh m₁ p
      have h₂ := stateSplit_logic_getD thresh m₂ p
      simp only [ht, ↓reduceIte] at h₁ h₂
      have heq := hlogic p
      rw [h₁, h₂] at heq
      simp only [Nat.min_def] at heq
      split_ifs at heq with h₃ h₄ <;> omega

end DataIrrelevance

/-! ## Cycle repetition (Theorem 2 from the paper) -/

/-- The key invariant maintained across steps within a cycle repetition.
    For each register `p`, either two states agree on its value, or both
    have values ≥ `margin * maxDenom prog p` — high enough that the register
    cannot affect which fraction fires.

    At step `t` within a cycle of length `cycleLen`, the margin is
    `cycleLen - t`. Since each step can decrease a register by at most
    `maxDenom`, the margin decreases by 1 each step. As long as `margin ≥ 1`
    (i.e., `t < cycleLen`), registers in the "differ" branch stay ≥ maxDenom,
    ensuring `data_irrelevant` applies. -/
def CycleInvariant (prog : List (RegMap × RegMap)) (margin : ℕ)
    (m₁ m₂ : RegMap) : Prop :=
  ∀ p, m₁.getD p 0 = m₂.getD p 0 ∨
       (m₁.getD p 0 ≥ margin * maxDenom prog p ∧
        m₂.getD p 0 ≥ margin * maxDenom prog p)

/-- `CycleInvariant` with `margin ≥ 1` implies `data_irrelevant`'s preconditions. -/
theorem cycleInvariant_implies_data_irrelevant
    (prog : List (RegMap × RegMap)) (margin : ℕ) (hmargin : 1 ≤ margin)
    (m₁ m₂ : RegMap) (hinv : CycleInvariant prog margin m₁ m₂) :
    (∀ p, m₁.getD p 0 < maxDenom prog p → m₁.getD p 0 = m₂.getD p 0) ∧
    (∀ p, m₁.getD p 0 ≥ maxDenom prog p → m₂.getD p 0 ≥ maxDenom prog p) := by
  constructor
  · intro p hlt
    rcases hinv p with h | ⟨h₁, _⟩
    · exact h
    · -- m₁ ≥ margin * maxDenom ≥ maxDenom > m₁: contradiction
      have : maxDenom prog p ≤ margin * maxDenom prog p :=
        le_mul_of_one_le_left (Nat.zero_le _) hmargin
      omega
  · intro p hge
    rcases hinv p with h | ⟨_, h₂⟩
    · omega
    · have : maxDenom prog p ≤ margin * maxDenom prog p :=
        le_mul_of_one_le_left (Nat.zero_le _) hmargin
      omega

/-- `stateSplit` logic agreement implies `CycleInvariant` with `margin = cycleLen`,
    where `thresh = dthreshMap prog cycleLen` (i.e., `thresh.getD p = cycleLen * maxDenom p`). -/
theorem stateSplit_implies_cycleInvariant
    (prog : List (RegMap × RegMap)) (cycleLen : ℕ)
    (thresh : RegMap) (m₁ m₂ : RegMap)
    (hthresh : ∀ p, thresh.getD p 0 = cycleLen * maxDenom prog p)
    (hlogic : ∀ p, (stateSplit thresh m₁).2.getD p 0 =
                    (stateSplit thresh m₂).2.getD p 0) :
    CycleInvariant prog cycleLen m₁ m₂ := by
  intro p
  have h₁ := stateSplit_logic_getD thresh m₁ p
  have h₂ := stateSplit_logic_getD thresh m₂ p
  have heq := hlogic p
  rw [hthresh p] at h₁ h₂
  -- Introduce t to avoid non-linear omega issues
  set t := cycleLen * maxDenom prog p with ht_def
  by_cases ht : t = 0
  · -- t = cycleLen * maxDenom = 0, so both values ≥ 0 = t
    right; constructor <;> omega
  · simp only [show (t : ℕ) ≠ 0 from ht, ↓reduceIte] at h₁ h₂
    rw [h₁, h₂] at heq
    simp only [Nat.min_def] at heq
    split_ifs at heq with h₃ h₄
    · left; omega
    · right; constructor <;> omega
    · right; constructor <;> omega
    · right; constructor <;> omega

/-- In a list with unique second components, two elements with the same
    second component are equal. -/
private theorem eq_of_mem_nodup_snd {α β : Type*}
    {l : List (α × β)} (hnodup : (l.map Prod.snd).Nodup)
    {a₁ a₂ : α × β} (h₁ : a₁ ∈ l) (h₂ : a₂ ∈ l) (heq : a₁.2 = a₂.2) :
    a₁ = a₂ := by
  induction l with
  | nil => simp at h₁
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp h₁ with rfl | h₁'
    · rcases List.mem_cons.mp h₂ with rfl | h₂'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨_, h₂', heq.symm⟩) hnodup.1
    · rcases List.mem_cons.mp h₂ with rfl | h₂'
      · exact absurd (List.mem_map.mpr ⟨_, h₁', heq⟩) hnodup.1
      · exact ih hnodup.2 h₁' h₂'

/-- When `elimStep` fires, the denominator of the chosen fraction is applicable
    to the state. In particular, `den.getD p 0 ≤ m.getD p 0` for all `p`. -/
theorem elimStep_den_le (cands : List Candidate) (m : RegMap)
    (hnodup : (cands.map (·.2)).Nodup)
    (i : ℕ) (m' : RegMap) (h : elimStep cands m = some (i, m'))
    (num den : RegMap) (hmem : ((num, den), i) ∈ cands) (p : ℕ) :
    den.getD p 0 ≤ m.getD p 0 := by
  -- elimStep fires the first applicable fraction. Since indices are unique
  -- and the result has index i, the entry ((num, den), i) must be the one
  -- that fired, meaning applicable den m = true.
  simp only [elimStep] at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, ⟨⟨num', den'⟩, idx'⟩, _, hd, hfire, _⟩ := h
  have happ : RegMap.applicable den' m = true := by
    by_contra hc; simp [Bool.not_eq_true] at hc; simp [hc] at hfire
  simp only [happ, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hfire
  have hmem' : ((num', den'), idx') ∈ cands := by
    rw [hd]; exact List.mem_append_right _ (List.mem_cons_self ..)
  rw [show idx' = i from hfire.1] at hmem'
  have hsame := eq_of_mem_nodup_snd hnodup hmem hmem' rfl
  simp only [Prod.mk.injEq] at hsame
  obtain ⟨⟨_, rfl⟩, _⟩ := hsame
  -- Now den = den', and applicable den m = true
  -- applicable means: den.all (fun p e => m.get p ≥ e) = true
  -- For our specific p: den.getD p 0 ≤ m.getD p 0
  rw [RegMap.applicable_eq_toList_all] at happ
  by_cases hp : p ∈ den
  · have hget := Std.TreeMap.getElem?_eq_some_getD_of_contains
                   ((Std.TreeMap.contains_iff_mem).mpr hp) (fallback := 0)
    have hmem_list := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mpr hget
    have hall := List.all_eq_true.mp happ _ hmem_list
    exact decide_eq_true_eq.mp hall
  · rw [Std.TreeMap.getD_eq_fallback hp]; exact Nat.zero_le _

/-- If `elimStep` returns the same index on two inputs, and candidates have unique
    indices, both results come from applying the same fraction. -/
theorem elimStep_common_frac (cands : List Candidate) (m₁ m₂ : RegMap)
    (hnodup : (cands.map (·.2)).Nodup)
    (i : ℕ) (m₁' m₂' : RegMap)
    (h₁ : elimStep cands m₁ = some (i, m₁'))
    (h₂ : elimStep cands m₂ = some (i, m₂')) :
    ∃ num den, ((num, den), i) ∈ cands ∧
      m₁' = num.applyFrac den m₁ ∧ m₂' = num.applyFrac den m₂ := by
  simp only [elimStep] at h₁ h₂
  rw [List.findSome?_eq_some_iff] at h₁ h₂
  obtain ⟨_, ⟨⟨num₁, den₁⟩, idx₁⟩, _, hd₁, hf₁, _⟩ := h₁
  obtain ⟨_, ⟨⟨num₂, den₂⟩, idx₂⟩, _, hd₂, hf₂, _⟩ := h₂
  have ha₁ : RegMap.applicable den₁ m₁ = true := by
    by_contra h; simp [Bool.not_eq_true] at h; simp [h] at hf₁
  have ha₂ : RegMap.applicable den₂ m₂ = true := by
    by_contra h; simp [Bool.not_eq_true] at h; simp [h] at hf₂
  simp only [ha₁, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hf₁
  simp only [ha₂, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hf₂
  have hmem₁ : ((num₁, den₁), idx₁) ∈ cands := by
    rw [hd₁]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hmem₂ : ((num₂, den₂), idx₂) ∈ cands := by
    rw [hd₂]; exact List.mem_append_right _ (List.mem_cons_self ..)
  -- Both entries have index i, so they're the same entry (indices are unique)
  rw [show idx₁ = i from hf₁.1] at hmem₁
  rw [show idx₂ = i from hf₂.1] at hmem₂
  have hsame := eq_of_mem_nodup_snd hnodup hmem₁ hmem₂ rfl
  simp only [Prod.mk.injEq] at hsame
  obtain ⟨⟨rfl, rfl⟩, _⟩ := hsame
  exact ⟨num₁, den₁, hmem₁, hf₁.2.symm, hf₂.2.symm⟩

/-- Extracting fraction components from an `elimStep` result.
    If `elimStep cands m = some (i, m')`, then there exist `num, den` from `prog`
    such that `m' = applyFrac num den m` and `den.getD p ≤ maxDenom prog p`. -/
theorem elimStep_exists_frac (prog : List (RegMap × RegMap))
    (cands : List Candidate) (m : RegMap)
    (hcands : ∀ c ∈ cands, c.1 ∈ prog)
    (i : ℕ) (m' : RegMap)
    (hstep : elimStep cands m = some (i, m')) :
    ∃ num den, (num, den) ∈ prog ∧
      m' = RegMap.applyFrac num den m ∧
      ∀ p, den.getD p 0 ≤ maxDenom prog p := by
  simp only [elimStep] at hstep
  rw [List.findSome?_eq_some_iff] at hstep
  obtain ⟨_, ⟨⟨num, den⟩, idx⟩, _, hdecomp, hfire, _⟩ := hstep
  have happ : RegMap.applicable den m = true := by
    by_contra h; simp [Bool.not_eq_true] at h; simp [h] at hfire
  simp only [happ, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hfire
  have hmem : ((num, den), idx) ∈ cands := by
    rw [hdecomp]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hprog : (num, den) ∈ prog := hcands _ hmem
  exact ⟨num, den, hprog, hfire.2.symm, fun p => maxDenom_ge prog num den hprog p⟩

/-- One `elimStep` preserves the `CycleInvariant`, decreasing the margin by 1.
    When the same fraction fires on both states (guaranteed by `data_irrelevant`),
    registers that agreed still agree (by `applyFrac_getD_eq`), and registers
    that differed both decrease by at most `maxDenom`. -/
theorem elimStep_preserves_cycleInvariant
    (prog : List (RegMap × RegMap)) (margin : ℕ) (hmargin : 2 ≤ margin)
    (cands : List Candidate) (m₁ m₂ : RegMap)
    (hcands : ∀ c ∈ cands, c.1 ∈ prog)
    (hnodup : (cands.map (·.2)).Nodup)
    (hinv : CycleInvariant prog margin m₁ m₂)
    (i : ℕ) (m₁' m₂' : RegMap)
    (h₁ : elimStep cands m₁ = some (i, m₁'))
    (h₂ : elimStep cands m₂ = some (i, m₂')) :
    CycleInvariant prog (margin - 1) m₁' m₂' := by
  obtain ⟨num, den, hmem_cands, hm₁', hm₂'⟩ :=
    elimStep_common_frac cands m₁ m₂ hnodup i m₁' m₂' h₁ h₂
  have hprog : (num, den) ∈ prog := hcands _ hmem_cands
  intro p
  rcases hinv p with heq | ⟨h₁_ge, h₂_ge⟩
  · -- Registers agreed: still agree after applying the same fraction
    left
    rw [hm₁', hm₂']
    exact applyFrac_getD_eq num den m₁ m₂ p heq
  · -- Registers differed but both ≥ margin * maxDenom.
    -- After applying fraction: value = old - den + num ≥ margin*md - md = (margin-1)*md
    right
    have hden_le : den.getD p 0 ≤ maxDenom prog p := maxDenom_ge prog num den hprog p
    rw [hm₁', hm₂', applyFrac_getD, applyFrac_getD]
    -- Introduce local vars to help omega with non-linear terms
    set md := maxDenom prog p
    set mm := margin * md
    set mm1 := (margin - 1) * md
    have hmm_ge_md : md ≤ mm :=
      le_mul_of_one_le_left (Nat.zero_le _) (by omega : 1 ≤ margin)
    have hmm1_eq : mm = mm1 + md := by
      simp only [mm, mm1]
      conv_lhs => rw [show margin = (margin - 1) + 1 from by omega]
      rw [Nat.add_mul, Nat.one_mul]
    have hmm1_le : mm1 ≤ mm - md := by omega
    -- Chain: m ≥ mm ≥ md ≥ den, so m - den ≥ mm - md ≥ mm1
    have h₁_sub : m₁.getD p 0 - den.getD p 0 ≥ mm - md := by omega
    have h₂_sub : m₂.getD p 0 - den.getD p 0 ≥ mm - md := by omega
    constructor <;> omega

/-- The sequence of fraction indices fired during `k` steps from state `m`,
    using the elimination interpreter. -/
def fracSequence (table : Array (List Candidate))
    (fallback : List Candidate)
    (m : RegMap) (cands : List Candidate) : ℕ → List ℕ
  | 0 => []
  | k + 1 =>
    match elimStep cands m with
    | none => []
    | some (i, m') =>
      let nextCands := if h : i < table.size then table[i] else fallback
      i :: fracSequence table fallback m' nextCands k

/-- Well-formedness condition for the candidate table: every entry comes from
    `prog` and has unique indices. This holds for `optTable` and `allCandidates`. -/
def CandidatesWF (prog : List (RegMap × RegMap))
    (table : Array (List Candidate)) (fallback : List Candidate) : Prop :=
  (∀ i, (h : i < table.size) → (∀ c ∈ table[i], c.1 ∈ prog) ∧ (table[i].map (·.2)).Nodup) ∧
  (∀ c ∈ fallback, c.1 ∈ prog) ∧ (fallback.map (·.2)).Nodup

/-- **Theorem (Cycle repetition).**
    If two states satisfy `CycleInvariant` with `margin = k`, and the same
    candidate list is used, then the same fraction sequence fires for `k` steps.

    This is the core of Theorem 2 in the paper. The proof proceeds by induction
    on `k`, using `data_irrelevant` + `elimStep_preserves_cycleInvariant` at each
    step. The candidate list changes in the same way for both states (same index
    fires → same next candidates), maintaining all invariants. -/
theorem cycle_same_fracs (prog : List (RegMap × RegMap))
    (table : Array (List Candidate))
    (fallback : List Candidate)
    (cands : List Candidate) (m₁ m₂ : RegMap)
    (hcands : ∀ c ∈ cands, c.1 ∈ prog)
    (hnodup : (cands.map (·.2)).Nodup)
    (hwf : CandidatesWF prog table fallback)
    (k : ℕ) (hk : 0 < k)
    (hinv : CycleInvariant prog k m₁ m₂) :
    fracSequence table fallback m₁ cands k =
    fracSequence table fallback m₂ cands k := by
  induction k generalizing cands m₁ m₂ with
  | zero => omega
  | succ k ih =>
    simp only [fracSequence]
    -- data_irrelevant gives same fraction index
    have ⟨hlogic, hdata⟩ := cycleInvariant_implies_data_irrelevant prog (k + 1)
      (by omega) m₁ m₂ hinv
    have hdi := data_irrelevant prog cands m₁ m₂ hcands hlogic hdata
    -- Case split on elimStep results
    cases h₁ : elimStep cands m₁ with
    | none =>
      -- m₁ halts: data_irrelevant says m₂ must give same index (none)
      have : (elimStep cands m₂).map Prod.fst = none := by
        rw [← hdi]; simp [h₁]
      cases h₂ : elimStep cands m₂ with
      | none => rfl
      | some p => simp [h₂] at this
    | some p =>
      obtain ⟨idx, m₁'⟩ := p
      -- data_irrelevant gives same fraction index on m₂
      have hdi_idx : (elimStep cands m₂).map Prod.fst = some idx := by
        rw [← hdi]; simp [h₁]
      -- Extract m₂' such that elimStep cands m₂ = some (idx, m₂')
      have ⟨m₂', h₂⟩ : ∃ m₂', elimStep cands m₂ = some (idx, m₂') := by
        cases h₂ : elimStep cands m₂ with
        | none => simp [h₂] at hdi_idx
        | some q =>
          have : q.1 = idx := by
            simp only [h₂, Option.map_some] at hdi_idx; exact Option.some.inj hdi_idx
          exact ⟨q.2, by rw [← this, Prod.mk.eta]⟩
      -- Unfold fracSequence on both sides and simplify
      simp only [h₂]
      -- Goal: idx :: fracSequence ... m₁' ... k = idx :: fracSequence ... m₂' ... k
      congr 1
      cases k with
      | zero => simp [fracSequence]
      | succ k' =>
        have hinv' := elimStep_preserves_cycleInvariant prog (k' + 2) (by omega)
          cands m₁ m₂ hcands hnodup (show CycleInvariant prog (k' + 2) m₁ m₂ by
            convert hinv using 1) idx m₁' m₂' h₁ h₂
        simp only [show k' + 2 - 1 = k' + 1 from by omega] at hinv'
        set nextCands := if h : idx < table.size then table[idx] else fallback
        have hcands' : ∀ c ∈ nextCands, c.1 ∈ prog := by
          simp only [nextCands]; split
          · next h => exact (hwf.1 idx h).1
          · exact hwf.2.1
        have hnodup' : (nextCands.map (·.2)).Nodup := by
          simp only [nextCands]; split
          · next h => exact (hwf.1 idx h).2
          · exact hwf.2.2
        exact ih _ m₁' m₂' hcands' hnodup' (by omega) hinv'

/-! ## Leap correctness -/

/-- The per-register change from `applyFrac` is state-independent:
    applying the same fraction to any two states gives the same integer delta.
    This is the foundation for proving that repeated cycles are additive. -/
theorem applyFrac_delta_eq (num den m₁ m₂ : RegMap) (p : ℕ)
    (h₁ : den.getD p 0 ≤ m₁.getD p 0) (h₂ : den.getD p 0 ≤ m₂.getD p 0) :
    (num.applyFrac den m₁).getD p 0 - m₁.getD p 0 =
    (num.applyFrac den m₂).getD p 0 - m₂.getD p 0 := by
  simp only [applyFrac_getD]; omega

/-- Running one `elimStep` that fires the same fraction on two states
    produces the same per-register change, when both states have
    register values ≥ the denominator (no saturation). -/
theorem elimStep_delta_eq (cands : List Candidate) (m₁ m₂ : RegMap)
    (hnodup : (cands.map (·.2)).Nodup)
    (i : ℕ) (m₁' m₂' : RegMap)
    (h₁ : elimStep cands m₁ = some (i, m₁'))
    (h₂ : elimStep cands m₂ = some (i, m₂'))
    (p : ℕ)
    (hge₁ : ∀ (num den : RegMap), ((num, den), i) ∈ cands →
      den.getD p 0 ≤ m₁.getD p 0)
    (hge₂ : ∀ (num den : RegMap), ((num, den), i) ∈ cands →
      den.getD p 0 ≤ m₂.getD p 0) :
    m₁'.getD p 0 - m₁.getD p 0 = m₂'.getD p 0 - m₂.getD p 0 := by
  obtain ⟨num, den, hmem, hm₁', hm₂'⟩ := elimStep_common_frac cands m₁ m₂
    hnodup i m₁' m₂' h₁ h₂
  rw [hm₁', hm₂']
  exact applyFrac_delta_eq num den m₁ m₂ p (hge₁ num den hmem) (hge₂ num den hmem)

/-- Candidates from `elimRunAux` satisfy the WF conditions: entries come from
    `prog` and have unique indices. This is because at each step, `nextCands`
    is either `table[idx]` or `fallback`, both of which are WF by `CandidatesWF`. -/
theorem elimRunAux_cands_wf
    (prog : List (RegMap × RegMap))
    (table : Array (List Candidate))
    (fallback : List Candidate)
    (hwf : CandidatesWF prog table fallback)
    (m : RegMap) (cands : List Candidate)
    (hcands : ∀ c ∈ cands, c.1 ∈ prog)
    (hnodup : (cands.map (·.2)).Nodup)
    (k : ℕ) (m' : RegMap) (cands' : List Candidate)
    (hrun : elimRunAux table fallback m cands k = some (m', cands')) :
    (∀ c ∈ cands', c.1 ∈ prog) ∧ (cands'.map (·.2)).Nodup := by
  induction k generalizing m cands m' cands' with
  | zero =>
    simp only [elimRunAux, Option.some.injEq, Prod.mk.injEq] at hrun
    rw [← hrun.2]; exact ⟨hcands, hnodup⟩
  | succ k ih =>
    simp only [elimRunAux, bind, Option.bind] at hrun
    cases hprev : elimRunAux table fallback m cands k with
    | none => simp [hprev] at hrun
    | some prev =>
      obtain ⟨midM, midC⟩ := prev
      simp only [hprev] at hrun
      cases hstep : elimStep midC midM with
      | none => simp [hstep] at hrun
      | some result =>
        obtain ⟨idx, stepped⟩ := result
        simp only [hstep] at hrun
        cases hrun with | refl =>
        -- cands' = if idx < table.size then table[idx] else fallback
        split
        · next h => exact hwf.1 idx h
        · exact ⟨hwf.2.1, hwf.2.2⟩

/-- **Combined cycle properties: difference, candidates, and invariant.**
    Running k elimination steps from two states with `CycleInvariant prog margin m₁ m₂`
    (where `margin ≥ k + 1`) produces:
    (1) the same output candidate list,
    (2) preserved per-register difference (in ℤ), and
    (3) `CycleInvariant prog (margin - k) m₁' m₂'` between the output states.

    All three properties are proved together because they depend on each other
    at each inductive step:
    - Same candidates (1) is needed to apply `data_irrelevant` at the next step
    - The invariant (3) feeds into `data_irrelevant` + `elimStep_preserves_cycleInvariant`
    - Difference preservation (2) follows from the same fraction firing -/
theorem cycle_properties
    (prog : List (RegMap × RegMap))
    (table : Array (List Candidate))
    (fallback : List Candidate)
    (cands : List Candidate) (m₁ m₂ : RegMap)
    (hcands : ∀ c ∈ cands, c.1 ∈ prog)
    (hnodup : (cands.map (·.2)).Nodup)
    (hwf : CandidatesWF prog table fallback)
    (k margin : ℕ) (hmargin : k + 1 ≤ margin)
    (hinv : CycleInvariant prog margin m₁ m₂)
    (m₁' m₂' : RegMap) (cands₁' cands₂' : List Candidate)
    (hrun₁ : elimRunAux table fallback m₁ cands k = some (m₁', cands₁'))
    (hrun₂ : elimRunAux table fallback m₂ cands k = some (m₂', cands₂')) :
    cands₁' = cands₂' ∧
    (∀ p, (m₁'.getD p 0 : ℤ) - (m₂'.getD p 0 : ℤ) =
          (m₁.getD p 0 : ℤ) - (m₂.getD p 0 : ℤ)) ∧
    CycleInvariant prog (margin - k) m₁' m₂' := by
  induction k generalizing cands m₁ m₂ m₁' m₂' cands₁' cands₂' margin with
  | zero =>
    simp only [elimRunAux, Option.some.injEq, Prod.mk.injEq] at hrun₁ hrun₂
    obtain ⟨hm₁, hc₁⟩ := hrun₁
    obtain ⟨hm₂, hc₂⟩ := hrun₂
    subst hm₁; subst hm₂; subst hc₁; subst hc₂
    exact ⟨rfl, fun _ => rfl, by simp only [Nat.sub_zero]; exact hinv⟩
  | succ k ih =>
    -- Unfold elimRunAux (k+1) = do { prev ← elimRunAux k; step prev }
    simp only [elimRunAux, bind, Option.bind] at hrun₁ hrun₂
    -- Extract intermediate states from elimRunAux k
    cases hprev₁ : elimRunAux table fallback m₁ cands k with
    | none => simp [hprev₁] at hrun₁
    | some prev₁ =>
      obtain ⟨mid₁, midCands₁⟩ := prev₁
      simp only [hprev₁] at hrun₁
      cases hprev₂ : elimRunAux table fallback m₂ cands k with
      | none => simp [hprev₂] at hrun₂
      | some prev₂ =>
        obtain ⟨mid₂, midCands₂⟩ := prev₂
        simp only [hprev₂] at hrun₂
        -- IH gives all three properties for the first k steps
        -- Call IH with the same margin: after k steps, CycleInvariant (margin - k)
        have ⟨hcands_eq, hdiff_k, hinv_mid⟩ := ih cands m₁ m₂ (margin := margin)
          hcands hnodup (by omega) hinv mid₁ mid₂ midCands₁ midCands₂ hprev₁ hprev₂
        -- hinv_mid : CycleInvariant prog (margin - k) mid₁ mid₂
        -- Since margin ≥ k + 2, margin - k ≥ 2
        -- data_irrelevant gives same fraction index (needs margin - k ≥ 1)
        have ⟨hlogic_mid, hdata_mid⟩ :=
          cycleInvariant_implies_data_irrelevant prog (margin - k)
            (by omega) mid₁ mid₂ hinv_mid
        -- Rewrite to use the same candidate list
        rw [hcands_eq] at hrun₁
        -- Need hcands and hnodup for midCands₂
        have ⟨hcands_mid, hnodup_mid⟩ :=
          elimRunAux_cands_wf prog table fallback hwf m₂ cands hcands hnodup
            k mid₂ midCands₂ hprev₂
        have hdi := data_irrelevant prog midCands₂ mid₁ mid₂
          hcands_mid hlogic_mid hdata_mid
        -- Case split on elimStep results
        cases hstep₁ : elimStep midCands₂ mid₁ with
        | none =>
          simp [hstep₁] at hrun₁
        | some result₁ =>
          obtain ⟨idx₁, stepped₁⟩ := result₁
          simp only [hstep₁] at hrun₁
          cases hstep₂ : elimStep midCands₂ mid₂ with
          | none =>
            -- data_irrelevant says same index, contradiction
            have : (elimStep midCands₂ mid₂).map Prod.fst = some idx₁ := by
              rw [← hdi]; simp [hstep₁]
            simp [hstep₂] at this
          | some result₂ =>
            obtain ⟨idx₂, stepped₂⟩ := result₂
            simp only [hstep₂] at hrun₂
            -- Same index
            have hidx : idx₁ = idx₂ := by
              have h₁ : (elimStep midCands₂ mid₁).map Prod.fst = some idx₁ := by
                simp [hstep₁]
              have h₂ : (elimStep midCands₂ mid₂).map Prod.fst = some idx₂ := by
                simp [hstep₂]
              rw [← hdi] at h₂; rw [h₁] at h₂
              exact Option.some.inj h₂
            subst hidx
            -- Same fraction (num, den)
            obtain ⟨num, den, hmem, hm₁eq, hm₂eq⟩ :=
              elimStep_common_frac midCands₂ mid₁ mid₂ hnodup_mid
                idx₁ stepped₁ stepped₂ hstep₁ hstep₂
            -- hrun₁ : some (stepped₁, nextCands) = some (m₁', cands₁')
            -- hrun₂ : some (stepped₂, nextCands) = some (m₂', cands₂')
            -- where nextCands = if h : idx₁ < table.size then table[idx₁] else fallback
            -- Use injection to extract
            cases hrun₁ with | refl =>
            cases hrun₂ with | refl =>
            -- Now m₁' = stepped₁, m₂' = stepped₂, cands₁' = cands₂' = nextCands
            refine ⟨rfl, ?_, ?_⟩
            · -- Difference preserved
              intro q
              rw [hm₁eq, hm₂eq, applyFrac_getD, applyFrac_getD]
              have := hdiff_k q
              -- Need den.getD q 0 ≤ mid.getD q 0 for the ℕ→ℤ cast
              have hle₁ := elimStep_den_le midCands₂ mid₁ hnodup_mid
                idx₁ m₁' hstep₁ num den hmem q
              have hle₂ := elimStep_den_le midCands₂ mid₂ hnodup_mid
                idx₁ m₂' hstep₂ num den hmem q
              push_cast [Nat.cast_sub hle₁, Nat.cast_sub hle₂]
              omega
            · -- CycleInvariant prog (margin - (k + 1))
              -- hinv_mid : CycleInvariant prog (margin - k) mid₁ mid₂
              -- margin - k ≥ 2 (from hmargin : k + 2 ≤ margin)
              -- elimStep_preserves gives CycleInvariant (margin - k - 1) = (margin - (k+1))
              exact elimStep_preserves_cycleInvariant prog (margin - k)
                (by omega) midCands₂ mid₁ mid₂ hcands_mid hnodup_mid
                hinv_mid idx₁ m₁' m₂' hstep₁ hstep₂

/-! ### Proof roadmap for full leap correctness

The remaining path from `cycle_properties` to a full leap correctness theorem
(`Correct` for the cycle-detecting interpreter with leaping) requires:

1. **Repeated cycle linearity:** By induction on `c`, applying `cycle_properties`
   at each cycle boundary to show that after `c` cycles from m₀, register `p`
   has value `m₀.getD p 0 + c * delta_p` (in ℤ) where `delta_p` is the
   one-cycle change. The `CycleInvariant` margin decreases by `cycleLen` per
   cycle, requiring an initial margin of `c * cycleLen + 1`.

2. **Bridge to `leapState`:** Show that the linear formula matches the
   `leapState` computation: `newData_p = endData_p + c * (endData_p - startData_p)`
   where `startData` and `endData` are the data components from `stateSplit`.

3. **Bridge to `naiveRun`:** Use `regRun_eq` and `facmap_unfmap` to convert
   the RegMap-level result back to a statement about `naiveRun`.

4. **Wire leaping into `cycleRunAux`:** Modify `cycleRunAux` to actually
   detect cycles and leap (the TODO at line ~950), then re-prove
   `cycleRun_correct` using `leap_correct`.

Each step is straightforward given `cycle_properties` but involves significant
bookkeeping. The mathematical core — that cycles are additive and same fractions
fire under `CycleInvariant` — is fully proved.
-/

/-! ## The cycle-detecting interpreter -/

/-- Canonical comparison for RegMap (sorted key-value lists).
    Used by `CBuf.getRange` to detect repeated logic states. -/
instance : BEq RegMap where
  beq a b := a.toList == b.toList

/-- Max denominator per prime across all fractions. Corresponds to
    `dmaxes = M.unionsWith max $ map snd fmaps` in Fractran.hs. -/
def dmaxesMap (prog : List (RegMap × RegMap)) : RegMap :=
  prog.foldl (fun acc (_, den) =>
    den.foldl (fun a p e =>
      let cur := a.getD p 0
      if e > cur then a.insert p e else a) acc) ∅

/-- foldl with conditional max-insert: result at `p` is `acc.getD p 0` when `p` not in list. -/
private theorem den_foldl_max_not_mem (l : List (ℕ × ℕ)) (p : ℕ) (acc : RegMap)
    (hp : p ∉ l.map Prod.fst) :
    (l.foldl (fun (a : RegMap) (b : ℕ × ℕ) =>
      if b.2 > a.getD b.1 0 then a.insert b.1 b.2 else a) acc).getD p 0 =
    acc.getD p 0 := by
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hp
    simp only [List.foldl_cons]
    by_cases hcond : hd.2 > acc.getD hd.1 0
    · simp only [hcond, ↓reduceIte]
      rw [ih (acc.insert hd.1 hd.2) hp.2]
      rw [Std.TreeMap.getD_insert]
      have hne : compare hd.1 p ≠ .eq := fun h => hp.1 (compare_eq_iff_eq.mp h).symm
      simp [hne]
    · simp only [hcond, ↓reduceIte]
      exact ih acc hp.2

/-- foldl with conditional max-insert on `den.toList` gives `max acc.getD p 0 den.getD p 0`. -/
private theorem den_foldl_max_getD (den acc : RegMap) (p : ℕ) :
    (den.foldl (fun a q e =>
      let cur := a.getD q 0
      if e > cur then a.insert q e else a) acc).getD p 0 =
    max (acc.getD p 0) (den.getD p 0) := by
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  set l := den.toList
  have hnodup : (l.map Prod.fst).Nodup := by
    simp only [l, Std.TreeMap.map_fst_toList_eq_keys]
    exact Std.TreeMap.nodup_keys
  by_cases hp : p ∈ den
  · have hget := Std.TreeMap.getElem?_eq_some_getD_of_contains
                   ((Std.TreeMap.contains_iff_mem).mpr hp) (fallback := 0)
    have hmem := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mpr hget
    obtain ⟨l₁, l₂, hlist⟩ := List.mem_iff_append.mp hmem
    have hlist' : l = l₁ ++ (p, den.getD p 0) :: l₂ := hlist
    rw [hlist', List.map_append, List.map_cons] at hnodup
    rw [List.nodup_append] at hnodup
    obtain ⟨_, hnd_r, hdisj⟩ := hnodup
    have hp1 : p ∉ l₁.map Prod.fst := by
      intro h; exact absurd rfl (hdisj _ h p (List.mem_cons_self ..))
    have hp2 : p ∉ l₂.map Prod.fst := (List.nodup_cons.mp hnd_r).1
    rw [hlist', List.foldl_append, List.foldl_cons]
    set e := den.getD p 0
    -- Abbreviate `l₁.foldl ... acc` so all occurrences are unified
    set acc' := l₁.foldl (fun (a : RegMap) (b : ℕ × ℕ) =>
        if b.2 > a.getD b.1 0 then a.insert b.1 b.2 else a) acc with hacc'_def
    have hacc'_p : acc'.getD p 0 = acc.getD p 0 := by
      rw [hacc'_def]; exact den_foldl_max_not_mem l₁ p acc hp1
    by_cases hcond : e > acc'.getD p 0
    · simp only [hcond, ↓reduceIte]
      rw [den_foldl_max_not_mem l₂ p (acc'.insert p e) hp2]
      rw [Std.TreeMap.getD_insert, show compare p p = .eq from compare_eq_iff_eq.mpr rfl]
      simp only [ite_true]
      omega
    · simp only [hcond, ↓reduceIte]
      rw [den_foldl_max_not_mem l₂ p acc' hp2]
      omega
  · have hp_l : p ∉ l.map Prod.fst := by
      rw [Std.TreeMap.map_fst_toList_eq_keys]
      exact fun hmem => hp (Std.TreeMap.mem_of_mem_keys hmem)
    rw [den_foldl_max_not_mem l p acc hp_l]
    rw [Std.TreeMap.getD_eq_fallback hp]
    omega

/-- `dmaxesMap prog` agrees with `maxDenom prog` per prime. -/
theorem dmaxesMap_spec (prog : List (RegMap × RegMap)) (p : ℕ) :
    (dmaxesMap prog).getD p 0 = maxDenom prog p := by
  unfold dmaxesMap maxDenom
  suffices h : ∀ (init : RegMap),
      (prog.foldl (fun acc (x : RegMap × RegMap) =>
        x.2.foldl (fun a q e =>
          let cur := a.getD q 0
          if e > cur then a.insert q e else a) acc) init).getD p 0 =
      prog.foldl (fun acc (x : RegMap × RegMap) => max acc (x.2.getD p 0)) (init.getD p 0) by
    have := h ∅
    rwa [Std.TreeMap.getD_emptyc] at this
  intro init
  induction prog generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨num, den⟩ := hd
    simp only [List.foldl_cons]
    rw [ih]
    rw [den_foldl_max_getD]

/-- Internal state threaded through the cycle-detecting interpreter. -/
structure CycleState where
  m : RegMap
  cands : List Candidate
  buf : CBuf (RegMap × RegMap)
  stepsSimulated : ℕ
  halted : Bool := false

/-- Buffer invariant: each entry in the circular buffer corresponds to a
    `stateSplit` of an actual execution state.

    Specifically, `buf.toList[i]` (newest-first) is `stateSplit thresh m_i`
    where `m_i` is the state at step `stepsSimulated - 1 - i`, i.e.:
    - `naiveRun prog n (stepsSimulated - 1 - i) = some (unfmap m_i)`
    - `m_i` is well-formed

    The length bound ensures `stepsSimulated - 1 - i` doesn't underflow. -/
def BufferInvariant (prog : FractranProg) (n : ℕ) (thresh : RegMap)
    (buf : CBuf (RegMap × RegMap)) (stepsSimulated : ℕ) : Prop :=
  buf.toList.length ≤ stepsSimulated ∧
  ∀ i (hi : i < buf.toList.length),
    ∃ m_i : RegMap,
      buf.toList[i] = stateSplit thresh m_i ∧
      naiveRun prog n (stepsSimulated - 1 - i) = some (RegMap.unfmap m_i) ∧
      RegMap.WF m_i

/-- Empty buffer trivially satisfies the buffer invariant. -/
theorem bufferInvariant_empty (prog : FractranProg) (n : ℕ) (thresh : RegMap)
    (cap : ℕ) (hcap : 0 < cap) (stepsSimulated : ℕ) :
    BufferInvariant prog n thresh (CBuf.empty cap hcap) stepsSimulated := by
  constructor
  · simp [CBuf.toList_empty]
  · intro i hi; simp [CBuf.toList_empty] at hi

/-- Inserting a new entry maintains the buffer invariant, provided the
    new entry is `stateSplit thresh m` for the current state. -/
theorem bufferInvariant_insert (prog : FractranProg) (n : ℕ) (thresh : RegMap)
    (buf : CBuf (RegMap × RegMap)) (stepsSimulated : ℕ) (m : RegMap)
    (hbuf : BufferInvariant prog n thresh buf stepsSimulated)
    (hm : naiveRun prog n stepsSimulated = some (RegMap.unfmap m))
    (hwf : RegMap.WF m) :
    BufferInvariant prog n thresh (buf.insert (stateSplit thresh m)) (stepsSimulated + 1) := by
  obtain ⟨hlen, hentries⟩ := hbuf
  set newBuf := buf.insert (stateSplit thresh m)
  have hlist : newBuf.toList = (stateSplit thresh m :: buf.toList).take buf.cap :=
    CBuf.toList_insert buf (stateSplit thresh m)
  constructor
  · -- Length bound
    rw [CBuf.toList_length, CBuf.len_insert]
    rw [CBuf.toList_length] at hlen
    omega
  · intro i hi
    -- Rewrite the list using our knowledge
    have hi' : i < ((stateSplit thresh m :: buf.toList).take buf.cap).length := by
      rwa [← hlist]
    have hgetEq : newBuf.toList[i] =
        ((stateSplit thresh m :: buf.toList).take buf.cap)[i] := by
      congr 1
    rw [hgetEq]
    cases i with
    | zero =>
      simp only [List.getElem_take, List.getElem_cons_zero]
      have : stepsSimulated + 1 - 1 - 0 = stepsSimulated := by omega
      exact ⟨m, rfl, this ▸ hm, hwf⟩
    | succ i =>
      have hi_len : i + 1 < ((stateSplit thresh m :: buf.toList).take buf.cap).length := hi'
      simp only [List.length_take, List.length_cons] at hi_len
      have hi_old : i < buf.toList.length := by omega
      simp only [List.getElem_take, List.getElem_cons_succ]
      obtain ⟨m_i, heq, hrun, hwf_i⟩ := hentries i hi_old
      have hstep_eq : stepsSimulated + 1 - 1 - (i + 1) = stepsSimulated - 1 - i := by omega
      exact ⟨m_i, heq, hstep_eq ▸ hrun, hwf_i⟩

/-- `regRun` decomposes additively: running `j + k` steps equals running `j` then `k`. -/
theorem regRun_add (prog : List (RegMap × RegMap)) (m : RegMap) (j k : ℕ) :
    regRun prog m (j + k) = regRun prog m j >>= fun m' => regRun prog m' k := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, regRun]
    cases regRun prog m j <;> simp [Option.bind]
  | succ k ih =>
    have : j + (k + 1) = j + k + 1 := by omega
    rw [this, regRun, ih]
    cases regRun prog m j <;> simp [Option.bind, regRun]

/-- `naiveRun` decomposes additively: running `j + k` steps equals running `j` then `k`. -/
theorem naiveRun_add (prog : FractranProg) (n : ℕ) (j k : ℕ) :
    naiveRun prog n (j + k) = naiveRun prog n j >>= fun m => naiveRun prog m k := by
  induction k with
  | zero =>
    simp only [Nat.add_zero, naiveRun]
    cases naiveRun prog n j <;> simp [Option.bind]
  | succ k ih =>
    have : j + (k + 1) = j + k + 1 := by omega
    rw [this, naiveRun, ih]
    cases naiveRun prog n j <;> simp [Option.bind, naiveRun]

/-! ### Leap correctness helper lemmas -/

/-- List.foldl of insert preserves membership and adds keys from the list. -/
private theorem mem_list_foldl_insert (l : List (ℕ × ℕ)) (acc : RegMap) (p : ℕ)
    (h : p ∈ acc ∨ p ∈ l.map Prod.fst) :
    p ∈ l.foldl (fun a (x : ℕ × ℕ) => a.insert x.1 0) acc := by
  induction l generalizing acc with
  | nil =>
    simp only [List.map_nil, List.not_mem_nil, or_false] at h
    exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.mem_cons] at h ⊢
    rcases h with h | (rfl | h)
    · exact ih _ (Or.inl (Std.TreeMap.mem_insert.mpr (Or.inr h)))
    · exact ih _ (Or.inl Std.TreeMap.mem_insert_self)
    · exact ih _ (Or.inr h)

/-- Outer foldl collecting denominator primes preserves membership. -/
private theorem mem_outer_foldl_of_mem (prog : List (RegMap × RegMap))
    (acc : RegMap) (p : ℕ) (hp : p ∈ acc) :
    p ∈ prog.foldl (fun acc' (_, den) =>
      den.foldl (fun a q _ => a.insert q 0) acc') acc := by
  induction prog generalizing acc with
  | nil => exact hp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [Std.TreeMap.foldl_eq_foldl_toList]
    exact mem_list_foldl_insert _ _ _ (Or.inl hp)

/-- If `p` is a key in some denominator in `prog`, then `p` is in the
    accumulated allDenPrimes map for any initial accumulator. -/
private theorem mem_allDenPrimes_of_mem_den (prog : List (RegMap × RegMap))
    (nd : RegMap × RegMap) (p : ℕ) (hp : p ∈ nd.2)
    (acc : RegMap) (hnd : nd ∈ prog) :
    p ∈ prog.foldl (fun acc' (_, den) =>
      den.foldl (fun a q _ => a.insert q 0) acc') acc := by
  induction prog generalizing acc with
  | nil => simp at hnd
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hnd with rfl | hnd
    · apply mem_outer_foldl_of_mem
      rw [Std.TreeMap.foldl_eq_foldl_toList]
      exact mem_list_foldl_insert _ _ _ (Or.inr (by
        rw [Std.TreeMap.map_fst_toList_eq_keys]; exact Std.TreeMap.mem_keys.mpr hp))
    · exact ih _ hnd

/-- `maxDenom` is zero when no denominator has a positive exponent for `p`. -/
private theorem maxDenom_eq_zero_of_forall (prog : List (RegMap × RegMap)) (p : ℕ)
    (h : ∀ nd ∈ prog, nd.2.getD p 0 = 0) :
    maxDenom prog p = 0 := by
  simp only [maxDenom]
  induction prog with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [h hd (List.mem_cons_self ..)]
    have : max 0 0 = 0 := rfl
    rw [this]
    exact ih (fun nd hnd => h nd (List.mem_cons.mpr (Or.inr hnd)))

/-- If `p ∉ allDenPrimes`, then `maxDenom prog p = 0`. -/
private theorem maxDenom_zero_of_not_allDenPrimes (prog : List (RegMap × RegMap)) (p : ℕ)
    (h : p ∉ prog.foldl (fun acc (_, den) =>
      den.foldl (fun a q _ => a.insert q 0) acc) (∅ : RegMap)) :
    maxDenom prog p = 0 := by
  apply maxDenom_eq_zero_of_forall
  intro nd hnd
  by_contra hne
  apply h
  have hp : p ∈ nd.2 := by
    by_contra hp
    exact hne (Std.TreeMap.getD_eq_fallback hp)
  exact mem_allDenPrimes_of_mem_den prog nd p hp ∅ hnd

/-- `dthreshMap` spec: `(dthreshMap prog cycleLen).getD p 0 = cycleLen * maxDenom prog p`. -/
theorem dthreshMap_spec (prog : List (RegMap × RegMap)) (cycleLen : ℕ) (p : ℕ) :
    (dthreshMap prog cycleLen).getD p 0 = cycleLen * maxDenom prog p := by
  simp only [dthreshMap, dthresh]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  set allDP := prog.foldl (fun acc (_, den) =>
    den.foldl (fun a q _ => a.insert q 0) acc) (∅ : RegMap)
  set l := allDP.toList
  have hnodup : (l.map Prod.fst).Nodup := by
    simp only [l, Std.TreeMap.map_fst_toList_eq_keys]; exact Std.TreeMap.nodup_keys
  by_cases hp : p ∈ allDP
  · -- p ∈ allDP: split l around p and compute directly
    have hget := Std.TreeMap.getElem?_eq_some_getD_of_contains
                   ((Std.TreeMap.contains_iff_mem).mpr hp) (fallback := 0)
    have hmem := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mpr hget
    obtain ⟨l₁, l₂, hlist⟩ := List.mem_iff_append.mp hmem
    have hlist' : l = l₁ ++ (p, allDP.getD p 0) :: l₂ := hlist
    rw [hlist', List.map_append, List.map_cons] at hnodup
    rw [List.nodup_append] at hnodup
    obtain ⟨hnd1, hnd_r, hdisj⟩ := hnodup
    have hp1 : p ∉ l₁.map Prod.fst := by
      intro h; exact absurd rfl (hdisj _ h p (List.mem_cons_self ..))
    have hp2 : p ∉ l₂.map Prod.fst := (List.nodup_cons.mp hnd_r).1
    have hnd2 : (l₂.map Prod.fst).Nodup := (List.nodup_cons.mp hnd_r).2
    rw [hlist', List.foldl_append, List.foldl_cons]
    -- After l₂: p is preserved (not in l₂)
    rw [foldl_cond_insert_getD_gen l₂ (fun q _ => cycleLen * maxDenom prog q) p _ hnd2 hp2]
    -- At the (p, _) step: either insert or skip
    by_cases hv : cycleLen * maxDenom prog p = 0
    · simp only [hv, ↓reduceIte]
      rw [foldl_cond_insert_getD_gen l₁ (fun q _ => cycleLen * maxDenom prog q) p ∅ hnd1 hp1]
      simp [Std.TreeMap.getD_emptyc]
    · simp only [hv, ↓reduceIte]
      rw [Std.TreeMap.getD_insert, show compare p p = .eq from compare_eq_iff_eq.mpr rfl]
      simp
  · -- p ∉ allDP: foldl doesn't touch p, and maxDenom = 0
    have hp_l : p ∉ l.map Prod.fst := by
      rw [Std.TreeMap.map_fst_toList_eq_keys]
      exact fun hmem => hp (Std.TreeMap.mem_of_mem_keys hmem)
    rw [foldl_cond_insert_getD_gen l (fun q _ => cycleLen * maxDenom prog q) p ∅ hnodup hp_l]
    simp only [Std.TreeMap.getD_emptyc]
    rw [maxDenom_zero_of_not_allDenPrimes prog p hp, Nat.mul_zero]

/-- If two `RegMap`s have equal `toList`, they agree on `getElem?`. -/
theorem getElem?_eq_of_toList_eq (m₁ m₂ : RegMap)
    (h : m₁.toList = m₂.toList) (p : ℕ) :
    m₁[p]? = m₂[p]? := by
  cases hv₁ : m₁[p]? with
  | none =>
    cases hv₂ : m₂[p]? with
    | none => rfl
    | some v₂ =>
      have := (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hv₂)
      rw [← h] at this
      have := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp this
      simp [hv₁] at this
  | some v₁ =>
    have hmem : (p, v₁) ∈ m₁.toList :=
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hv₁
    rw [h] at hmem
    exact (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hmem).symm

/-- If two `RegMap`s have equal `toList`, they agree on `getD`. -/
theorem getD_eq_of_toList_eq (m₁ m₂ : RegMap)
    (h : m₁.toList = m₂.toList) (p : ℕ) (d : ℕ) :
    m₁.getD p d = m₂.getD p d := by
  simp only [Std.TreeMap.getD_eq_getD_getElem?,
             getElem?_eq_of_toList_eq m₁ m₂ h p]

/-- The `allCandidates` list satisfies the membership and nodup conditions. -/
private theorem allCandidates_mem_prog (prog : List (RegMap × RegMap)) :
    ∀ c ∈ allCandidates prog, c.1 ∈ prog :=
  fun _ hc => List.fst_mem_of_mem_zipIdx hc

private theorem allCandidates_nodup_snd (prog : List (RegMap × RegMap)) :
    ((allCandidates prog).map (·.2)).Nodup := by
  unfold allCandidates
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' ..

/-- The `optTable`/`allCandidates` pair satisfies `CandidatesWF`. -/
private theorem candidatesWF_optTable (prog : List (RegMap × RegMap)) :
    CandidatesWF prog (optTable prog) (allCandidates prog) := by
  refine ⟨fun i hi => ?_, allCandidates_mem_prog prog, allCandidates_nodup_snd prog⟩
  rw [optTable_size] at hi
  simp only [optTable, Array.getElem_ofFn, List.splitAt_eq]
  constructor
  · -- Every candidate in entry has c.1 ∈ prog
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact allCandidates_mem_prog prog c
        ((List.filter_sublist.trans (List.take_sublist ..)).mem hc)
    · exact allCandidates_mem_prog prog c ((List.drop_sublist ..).mem hc)
  · -- Nodup indices
    have hnd := allCandidates_nodup_snd prog
    -- The entry (after simp) is filter p (take i ac) ++ drop i ac
    -- This is a sublist of take i ac ++ drop i ac = ac
    -- So (entry.map Prod.snd) is a sublist of (ac.map Prod.snd), which is nodup
    have key : ∀ (p : Candidate → Bool) (ac : List Candidate),
        List.Sublist ((List.filter p (ac.take i) ++ ac.drop i).map Prod.snd)
                     (ac.map Prod.snd) := by
      intro p ac
      rw [List.map_append,
          show ac.map Prod.snd = (ac.take i).map Prod.snd ++ (ac.drop i).map Prod.snd from
            by rw [← List.map_append, List.take_append_drop]]
      exact List.Sublist.append (List.Sublist.map _ List.filter_sublist)
        (List.Sublist.refl _)
    exact (key _ _).nodup hnd

/-- If `elimRunAux` succeeds for `m₁` under `CycleInvariant`, it also succeeds
    for `m₂`. The same fraction fires at each step (by `data_irrelevant`),
    so `elimStep` produces `some` for both. -/
private theorem elimRunAux_succeeds_of_cycleInvariant
    (prog : List (RegMap × RegMap))
    (table : Array (List Candidate))
    (fallback : List Candidate)
    (cands : List Candidate) (m₁ m₂ : RegMap)
    (hcands : ∀ c ∈ cands, c.1 ∈ prog)
    (hnodup : (cands.map (·.2)).Nodup)
    (hwf : CandidatesWF prog table fallback)
    (k margin : ℕ) (hmargin : k + 1 ≤ margin)
    (hinv : CycleInvariant prog margin m₁ m₂)
    (m₁' : RegMap) (cands₁' : List Candidate)
    (hrun₁ : elimRunAux table fallback m₁ cands k = some (m₁', cands₁')) :
    ∃ m₂' cands₂', elimRunAux table fallback m₂ cands k = some (m₂', cands₂') := by
  induction k generalizing cands m₁ m₂ m₁' cands₁' margin with
  | zero =>
    simp only [elimRunAux] at hrun₁ ⊢
    exact ⟨m₂, cands, rfl⟩
  | succ k ih =>
    simp only [elimRunAux, bind, Option.bind] at hrun₁ ⊢
    cases hprev₁ : elimRunAux table fallback m₁ cands k with
    | none => simp [hprev₁] at hrun₁
    | some prev₁ =>
      obtain ⟨mid₁, midCands₁⟩ := prev₁
      simp only [hprev₁] at hrun₁
      -- By IH, elimRunAux also succeeds for m₂ after k steps
      have hmargin_k : k + 1 ≤ margin := by omega
      obtain ⟨mid₂, midCands₂, hprev₂⟩ :=
        ih cands m₁ m₂ hcands hnodup margin hmargin_k hinv mid₁ midCands₁ hprev₁
      simp only [hprev₂]
      -- Get CycleInvariant for mid₁, mid₂ from cycle_properties
      have ⟨hcands_eq, _, hinv_mid⟩ := cycle_properties prog table fallback
        cands m₁ m₂ hcands hnodup hwf k margin (by omega) hinv
        mid₁ mid₂ midCands₁ midCands₂ hprev₁ hprev₂
      -- data_irrelevant: same step fires for both
      have ⟨hlogic, hdata⟩ := cycleInvariant_implies_data_irrelevant
        prog (margin - k) (by omega) mid₁ mid₂ hinv_mid
      rw [hcands_eq] at hrun₁
      have hdi := data_irrelevant prog midCands₂ mid₁ mid₂
        (elimRunAux_cands_wf prog table fallback hwf m₂ cands hcands hnodup
          k mid₂ midCands₂ hprev₂).1
        hlogic hdata
      cases hstep₁ : elimStep midCands₂ mid₁ with
      | none => simp [hstep₁] at hrun₁
      | some result₁ =>
        obtain ⟨idx₁, stepped₁⟩ := result₁
        -- data_irrelevant says elimStep mid₂ also succeeds with same index
        have : (elimStep midCands₂ mid₂).map Prod.fst = some idx₁ := by
          rw [← hdi]; simp [hstep₁]
        cases hstep₂ : elimStep midCands₂ mid₂ with
        | none => simp [hstep₂] at this
        | some result₂ =>
          obtain ⟨idx₂, stepped₂⟩ := result₂
          exact ⟨stepped₂, _, rfl⟩

/-! ## Per-register cycle analysis (paper's approach to Theorem 2)

The paper proves cycle repetition by analyzing each register individually:
for each data register p, the cycle can be repeated as long as the per-register
intermediate values + cumulative shift `k * delta_p` stay ≥ `maxDenom prog p`.

This section formalizes that approach via `shifted_regStep`, `shifted_regRun`,
and `iterated_cycle_per_reg`. The older uniform-margin `iterated_cycle`
required initial margin ≥ `(c+1) * L + 1`, which is impractically large
(typically larger than the actual register values). The per-register approach
exactly mirrors the paper's `life_p = margin_p / |delta_p|` bound.
-/

/-- One step of a shifted state. Given `m₁`, `m₂` satisfying `data_irrelevant`'s
    preconditions, both `regStep` calls fire the same fraction and the
    per-register difference is preserved (in ℤ). -/
theorem shifted_regStep (prog : List (RegMap × RegMap))
    (m₁ m₂ m₁' : RegMap)
    (hlogic : ∀ p, m₁.getD p 0 < maxDenom prog p → m₁.getD p 0 = m₂.getD p 0)
    (hdata : ∀ p, m₁.getD p 0 ≥ maxDenom prog p → m₂.getD p 0 ≥ maxDenom prog p)
    (h₁ : regStep prog m₁ = some m₁') :
    ∃ m₂', regStep prog m₂ = some m₂' ∧
        ∀ p, (m₂'.getD p 0 : ℤ) - (m₁'.getD p 0 : ℤ) =
              (m₂.getD p 0 : ℤ) - (m₁.getD p 0 : ℤ) := by
  have hcands := allCandidates_mem_prog prog
  have hnodup := allCandidates_nodup_snd prog
  -- Convert regStep on m₁ to elimStep on allCandidates
  have hes_eq₁ : (elimStep (allCandidates prog) m₁).map Prod.snd = some m₁' := by
    rw [elimStep_allCandidates]; exact h₁
  rw [Option.map_eq_some_iff] at hes_eq₁
  obtain ⟨⟨i, m₁'_es⟩, hes₁_raw, hm₁_eq⟩ := hes_eq₁
  simp only at hm₁_eq
  -- hes₁_raw : elimStep ... = some (i, m₁'_es), hm₁_eq : m₁'_es = m₁'
  have hes₁ : elimStep (allCandidates prog) m₁ = some (i, m₁') := by
    rw [hes₁_raw, hm₁_eq]
  -- data_irrelevant gives same index for m₂
  have hdi := data_irrelevant prog (allCandidates prog) m₁ m₂ hcands hlogic hdata
  rw [hes₁] at hdi
  simp only [Option.map_some] at hdi
  -- hdi : some i = (elimStep ... m₂).map Prod.fst
  rw [eq_comm, Option.map_eq_some_iff] at hdi
  obtain ⟨⟨i', m₂'⟩, hes₂_raw, hi_eq⟩ := hdi
  simp only at hi_eq
  have hes₂ : elimStep (allCandidates prog) m₂ = some (i, m₂') := by
    rw [hes₂_raw, hi_eq]
  refine ⟨m₂', ?_, ?_⟩
  · -- regStep prog m₂ = some m₂'
    have h := elimStep_allCandidates prog m₂
    rw [hes₂] at h
    simpa using h.symm
  · intro p
    obtain ⟨num, den, hmem, hm₁'eq, hm₂'eq⟩ :=
      elimStep_common_frac (allCandidates prog) m₁ m₂ hnodup i m₁' m₂' hes₁ hes₂
    have hd₁ := elimStep_den_le (allCandidates prog) m₁ hnodup i m₁' hes₁ num den hmem p
    have hd₂ := elimStep_den_le (allCandidates prog) m₂ hnodup i m₂' hes₂ num den hmem p
    rw [hm₁'eq, hm₂'eq, applyFrac_getD, applyFrac_getD]
    push_cast [Nat.cast_sub hd₁, Nat.cast_sub hd₂]
    ring

/-- regStep preserves WF: if `regStep prog m = some m'` and `m` is WF and `prog`
    is well-formed at the RegMap level, then `m'` is WF. -/
theorem regStep_wf_preserve (prog : FractranProg) (hw : prog.WellFormed)
    (m m' : RegMap) (hm : m.WF) (h : regStep prog.toRegProg m = some m') : m'.WF := by
  exact regStep_wf prog m hm hw m' h

/-- `k` steps of a shifted state. If `m₁` runs `k` steps to `m_end₁`, and `m₂`
    is a "shifted" version of `m₁` such that the data_irrelevant preconditions
    hold at every intermediate state of `m₁`'s trajectory, then `m₂` also runs
    `k` steps successfully and the per-register difference is preserved. -/
theorem shifted_regRun (prog : FractranProg) (hw : prog.WellFormed)
    (m₁ m₂ : RegMap) (k : ℕ) (hwf₁ : m₁.WF) (hwf₂ : m₂.WF)
    (hsafe : ∀ i, i < k → ∀ m_i, RegMap.WF m_i →
              regRun prog.toRegProg m₁ i = some m_i →
              ∀ p, (m_i.getD p 0 < maxDenom prog.toRegProg p →
                      (m₁.getD p 0 : ℤ) = m₂.getD p 0) ∧
                   (m_i.getD p 0 ≥ maxDenom prog.toRegProg p →
                      (m_i.getD p 0 : ℤ) +
                        ((m₂.getD p 0 : ℤ) - (m₁.getD p 0 : ℤ)) ≥
                      maxDenom prog.toRegProg p))
    (m_end₁ : RegMap)
    (hrun₁ : regRun prog.toRegProg m₁ k = some m_end₁) :
    ∃ m_end₂, regRun prog.toRegProg m₂ k = some m_end₂ ∧ m_end₂.WF ∧
        ∀ p, (m_end₂.getD p 0 : ℤ) - (m_end₁.getD p 0 : ℤ) =
              (m₂.getD p 0 : ℤ) - (m₁.getD p 0 : ℤ) := by
  induction k generalizing m_end₁ with
  | zero =>
    refine ⟨m₂, ?_, hwf₂, ?_⟩
    · simp [regRun]
    · intro p
      simp only [regRun] at hrun₁
      have heq : m_end₁ = m₁ := (Option.some.inj hrun₁).symm
      rw [heq]
  | succ k ih =>
    -- Decompose regRun (k+1) = regRun k >>= regStep
    have hregk : regRun prog.toRegProg m₁ (k+1) =
                  regRun prog.toRegProg m₁ k >>= regStep prog.toRegProg := rfl
    rw [hregk] at hrun₁
    cases hmk : regRun prog.toRegProg m₁ k with
    | none => rw [hmk] at hrun₁; simp at hrun₁
    | some m_k =>
      rw [hmk] at hrun₁
      change regStep prog.toRegProg m_k = some m_end₁ at hrun₁
      have hwf_mk : m_k.WF := regRun_wf prog m₁ hwf₁ hw k m_k hmk
      -- IH gives us m_k_alt = regRun ... m₂ k = some _ with delta preserved
      have hsafe_ih : ∀ i, i < k → _ := fun i hi => hsafe i (by omega)
      obtain ⟨m_k_alt, hrun_alt_k, hwf_mk_alt, hdiff_k⟩ := ih hsafe_ih m_k hmk
      -- Apply shifted_regStep
      have hsafe_k := hsafe k (by omega) m_k hwf_mk hmk
      have hlogic_k : ∀ p, m_k.getD p 0 < maxDenom prog.toRegProg p →
                      m_k.getD p 0 = m_k_alt.getD p 0 := by
        intro p hp
        have hm₁m₂ := (hsafe_k p).1 hp
        have h := hdiff_k p
        omega
      have hdata_k : ∀ p, m_k.getD p 0 ≥ maxDenom prog.toRegProg p →
                      m_k_alt.getD p 0 ≥ maxDenom prog.toRegProg p := by
        intro p hp
        have hd := (hsafe_k p).2 hp
        have h := hdiff_k p
        omega
      obtain ⟨m_end₂, hstep_alt, hdiff_step⟩ :=
        shifted_regStep prog.toRegProg m_k m_k_alt m_end₁ hlogic_k hdata_k hrun₁
      have hwf_end₂ : m_end₂.WF :=
        regStep_wf prog m_k_alt hwf_mk_alt hw m_end₂ hstep_alt
      refine ⟨m_end₂, ?_, hwf_end₂, ?_⟩
      · show regRun prog.toRegProg m₂ (k+1) = some m_end₂
        change regRun prog.toRegProg m₂ k >>= regStep prog.toRegProg = some m_end₂
        rw [hrun_alt_k]
        change regStep prog.toRegProg m_k_alt = some m_end₂
        exact hstep_alt
      · intro p
        have hd_step := hdiff_step p
        have hd_k := hdiff_k p
        omega

/-- **Iterated cycle (per-register).** Given one cycle `m₀ → m₁` of length `L`,
    if the per-register safety condition holds for shift `c * delta`, then `c`
    additional cycles can safely fire (so `c + 1` total cycles). The final state
    has `m_c.getD p 0 = m₀.getD p 0 + (c + 1) * delta_p` for each register `p`.

    This formalizes Theorem 2 from the paper using its actual proof technique:
    per-register trajectory analysis rather than a uniform `CycleInvariant`. -/
theorem iterated_cycle_per_reg
    (prog : FractranProg) (hw : prog.WellFormed)
    (m₀ m₁ : RegMap) (L : ℕ)
    (hwf₀ : m₀.WF) (hwf₁ : m₁.WF)
    (hone : regRun prog.toRegProg m₀ L = some m₁)
    (c : ℕ)
    (hsafe : ∀ i, i < L → ∀ m_i, RegMap.WF m_i →
              regRun prog.toRegProg m₀ i = some m_i →
              ∀ p, (m_i.getD p 0 < maxDenom prog.toRegProg p →
                      (c : ℤ) * ((m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) = 0) ∧
                   (m_i.getD p 0 ≥ maxDenom prog.toRegProg p →
                      (m_i.getD p 0 : ℤ) +
                        (c : ℤ) * ((m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) ≥
                      maxDenom prog.toRegProg p)) :
    ∃ m_c, regRun prog.toRegProg m₀ (L * (c + 1)) = some m_c ∧ m_c.WF ∧
        ∀ p, (m_c.getD p 0 : ℤ) =
              (m₀.getD p 0 : ℤ) + ((c + 1 : ℕ) : ℤ) *
              ((m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) := by
  induction c with
  | zero =>
    refine ⟨m₁, ?_, hwf₁, ?_⟩
    · rw [Nat.zero_add, Nat.mul_one]; exact hone
    · intro p; push_cast; ring
  | succ c ih =>
    -- Derive hsafe for c (smaller shift) from hsafe for c+1
    have hsafe_ih : ∀ i, i < L → ∀ m_i, RegMap.WF m_i →
                    regRun prog.toRegProg m₀ i = some m_i →
                    ∀ p, (m_i.getD p 0 < maxDenom prog.toRegProg p →
                            (c : ℤ) * ((m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) = 0) ∧
                         (m_i.getD p 0 ≥ maxDenom prog.toRegProg p →
                            (m_i.getD p 0 : ℤ) +
                              (c : ℤ) * ((m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) ≥
                            maxDenom prog.toRegProg p) := by
      intro i hi m_i hwf_mi hrun_mi p
      have h := hsafe i hi m_i hwf_mi hrun_mi p
      refine ⟨?_, ?_⟩
      · intro hp
        have h1 := h.1 hp
        -- ((c+1 : ℕ) : ℤ) * delta = 0 → delta = 0 → c * delta = 0
        push_cast at h1 ⊢
        have hdelta : (m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ) = 0 := by
          rcases mul_eq_zero.mp h1 with hl | hr
          · linarith
          · exact hr
        rw [hdelta]; ring
      · intro hp
        have h2 := h.2 hp
        push_cast at h2 ⊢
        -- m_i + (c+1)*delta ≥ maxDenom → m_i + c*delta ≥ maxDenom
        -- Case delta ≥ 0: m_i + c*delta ≥ m_i ≥ maxDenom (from hp)
        -- Case delta < 0: c*delta ≥ (c+1)*delta, so m_i + c*delta ≥ m_i + (c+1)*delta ≥ maxDenom
        by_cases hdelta : (m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ) ≥ 0
        · have h3 : (c : ℤ) * ((m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) ≥ 0 := by positivity
          linarith
        · push Not at hdelta
          have h3 : (c : ℤ) * ((m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) ≥
                    ((c + 1 : ℕ) : ℤ) * ((m₁.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) := by
            push_cast
            nlinarith
          linarith
    obtain ⟨m_c, hrun_m_c, hwf_m_c, hdiff_m_c⟩ := ih hsafe_ih
    -- Apply shifted_regRun for one more cycle from m_c
    have hshift_safe : ∀ i, i < L → ∀ m_i, RegMap.WF m_i →
                       regRun prog.toRegProg m₀ i = some m_i →
                       ∀ p, (m_i.getD p 0 < maxDenom prog.toRegProg p →
                              (m₀.getD p 0 : ℤ) = m_c.getD p 0) ∧
                            (m_i.getD p 0 ≥ maxDenom prog.toRegProg p →
                              (m_i.getD p 0 : ℤ) +
                                ((m_c.getD p 0 : ℤ) - (m₀.getD p 0 : ℤ)) ≥
                              maxDenom prog.toRegProg p) := by
      intro i hi m_i hwf_mi hrun_mi p
      have h := hsafe i hi m_i hwf_mi hrun_mi p
      have hd_m_c := hdiff_m_c p
      -- m_c.getD p 0 = m₀.getD p 0 + (c+1) * delta (from hdiff_m_c, with c+1 outer)
      -- So m_c - m₀ = (c+1) * delta
      refine ⟨?_, ?_⟩
      · intro hp
        have h1 := h.1 hp
        push_cast at h1 hd_m_c ⊢
        linarith
      · intro hp
        have h2 := h.2 hp
        push_cast at h2 hd_m_c ⊢
        linarith
    obtain ⟨m_next, hrun_next, hwf_next, hdiff_next⟩ :=
      shifted_regRun prog hw m₀ m_c L hwf₀ hwf_m_c hshift_safe m₁ hone
    refine ⟨m_next, ?_, hwf_next, ?_⟩
    · -- regRun (L * (c+1+1)) = regRun (L*(c+1)) >>= regRun L
      have hadd : L * (c + 1 + 1) = L * (c + 1) + L := by ring
      rw [hadd, regRun_add, hrun_m_c]
      change regRun prog.toRegProg m_c L = some m_next
      exact hrun_next
    · intro p
      have hd_next := hdiff_next p
      have hd_m_c := hdiff_m_c p
      push_cast at hd_next hd_m_c ⊢
      linarith


/-- `leapState` per-register specification. The result at register `p` is
    the data part (advanced by `c` cycles) plus the logic part. -/
theorem leapState_spec (startData endData logic : RegMap) (c : ℕ) (p : ℕ) :
    (leapState startData endData logic c).getD p 0 =
      (if endData.getD p 0 ≥ startData.getD p 0
       then endData.getD p 0 + c * (endData.getD p 0 - startData.getD p 0)
       else endData.getD p 0 - c * (startData.getD p 0 - endData.getD p 0))
      + logic.getD p 0 := by
  simp only [leapState]
  rw [RegMap.mul_getD]
  congr 1
  -- Goal: (keys.foldl ... ∅).getD p 0 = if-then-else
  set merged := startData.foldl (fun acc q _ => acc.insert q 0) endData
  set gval : ℕ → ℕ := fun q =>
    if endData.getD q 0 ≥ startData.getD q 0
    then endData.getD q 0 + c * (endData.getD q 0 - startData.getD q 0)
    else endData.getD q 0 - c * (startData.getD q 0 - endData.getD q 0)
  -- Helper: foldl preserves getD for keys not in the list
  have gen_not_in : ∀ (ks : List ℕ) (acc : RegMap), p ∉ ks →
      (ks.foldl (fun acc' q =>
        let sv := startData.getD q 0; let ev := endData.getD q 0
        let nv := if ev ≥ sv then ev + c * (ev - sv) else ev - c * (sv - ev)
        if nv = 0 then acc' else acc'.insert q nv) acc).getD p 0 =
      acc.getD p 0 := by
    intro ks acc hp
    induction ks generalizing acc with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.mem_cons, not_or] at hp
      simp only [List.foldl_cons]
      have step : ∀ (a : RegMap),
          (let sv := startData.getD hd 0; let ev := endData.getD hd 0
           let nv := if ev ≥ sv then ev + c * (ev - sv) else ev - c * (sv - ev)
           if nv = 0 then a else a.insert hd nv).getD p 0 = a.getD p 0 := by
        intro a; dsimp only
        by_cases hv : gval hd = 0
        · simp only [gval] at hv; simp only [hv, ↓reduceIte]
        · simp only [gval] at hv; simp only [hv, ↓reduceIte]
          rw [Std.TreeMap.getD_insert]
          simp only [compare_eq_iff_eq, show hd ≠ p from fun h => hp.1 h.symm, ite_false]
      rw [ih _ hp.2, step]
  -- Convert the let-based foldl to use gval (definitionally equal)
  have hfoldl_eq : ∀ (ks : List ℕ) (acc : RegMap),
      ks.foldl (fun acc' q =>
        let sv := startData.getD q 0; let ev := endData.getD q 0
        let nv := if ev ≥ sv then ev + c * (ev - sv) else ev - c * (sv - ev)
        if nv = 0 then acc' else acc'.insert q nv) acc =
      ks.foldl (fun acc' q =>
        if gval q = 0 then acc' else acc'.insert q (gval q)) acc := by
    intro _ _; rfl
  -- General claim: characterize getD for foldl with conditional inserts
  have gen : ∀ (ks : List ℕ) (acc : RegMap), ks.Nodup → p ∉ ks →
      (ks.foldl (fun acc' q =>
        if gval q = 0 then acc' else acc'.insert q (gval q)) acc).getD p 0 =
      acc.getD p 0 := by
    intro ks acc hnd hp
    induction ks generalizing acc with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.mem_cons, not_or] at hp
      rw [List.nodup_cons] at hnd
      simp only [List.foldl_cons]
      rw [ih _ hnd.2 hp.2]
      by_cases hv : gval hd = 0
      · simp only [hv, ↓reduceIte]
      · simp only [hv, ↓reduceIte]
        rw [Std.TreeMap.getD_insert]
        simp only [compare_eq_iff_eq, show hd ≠ p from fun h => hp.1 h.symm, ite_false]
  -- Main proof
  set keys := merged.toList.map Prod.fst
  have hnodup : keys.Nodup := by
    simp only [keys, Std.TreeMap.map_fst_toList_eq_keys]; exact Std.TreeMap.nodup_keys
  rw [hfoldl_eq]
  by_cases hp : p ∈ keys
  · -- p ∈ keys: split the list around p
    obtain ⟨l₁, l₂, hlist⟩ := List.mem_iff_append.mp hp
    rw [hlist] at hnodup
    rw [List.nodup_append] at hnodup
    obtain ⟨hnd1, hnd_r, hdisj⟩ := hnodup
    have hp1 : p ∉ l₁ := by
      intro h; exact absurd rfl (hdisj p h p (List.mem_cons_self ..))
    have hp2 : p ∉ l₂ := (List.nodup_cons.mp hnd_r).1
    rw [show keys = l₁ ++ p :: l₂ from hlist, List.foldl_append, List.foldl_cons]
    -- After l₂: p preserved
    rw [gen l₂ _ (List.nodup_cons.mp hnd_r).2 hp2]
    -- At the p step
    by_cases hv : gval p = 0
    · -- gval p = 0: didn't insert
      simp only [hv, ↓reduceIte]
      rw [gen l₁ _ hnd1 hp1, Std.TreeMap.getD_emptyc]
      exact hv.symm
    · -- gval p ≠ 0: inserted
      simp only [hv, ↓reduceIte]
      exact Std.TreeMap.getD_insert_self
  · -- p ∉ keys: newData.getD p 0 = 0, and sv = ev = 0
    rw [gen keys _ hnodup hp, Std.TreeMap.getD_emptyc]
    -- Show gval p = 0 from p ∉ keys → sv = ev = 0
    have hp_not_merged : p ∉ merged := by
      simp only [keys, Std.TreeMap.map_fst_toList_eq_keys, Std.TreeMap.mem_keys] at hp
      exact hp
    have hp_ed : endData.getD p 0 = 0 :=
      Std.TreeMap.getD_eq_fallback (fun h => hp_not_merged (by
        simp only [merged, Std.TreeMap.foldl_eq_foldl_toList]
        exact mem_list_foldl_insert _ _ _ (Or.inl h)))
    have hp_sd : startData.getD p 0 = 0 :=
      Std.TreeMap.getD_eq_fallback (fun h => hp_not_merged (by
        simp only [merged, Std.TreeMap.foldl_eq_foldl_toList]
        exact mem_list_foldl_insert _ _ _ (Or.inr (by
          rw [Std.TreeMap.map_fst_toList_eq_keys]; exact Std.TreeMap.mem_keys.mpr h))))
    simp only [hp_ed, hp_sd]; rfl

/-- Helper: foldl that conditionally inserts keys from a list preserves WF,
    provided the list only contains prime keys and the accumulator is WF. -/
private theorem foldl_cond_insert_wf
    (l : List (ℕ × ℕ)) (init : RegMap) (hinit : RegMap.WF init)
    (hl : ∀ pe ∈ l, pe.1.Prime)
    (f : RegMap → ℕ → ℕ → RegMap)
    (hf : ∀ acc p e, f acc p e = acc ∨ ∃ v, f acc p e = acc.insert p v) :
    RegMap.WF (l.foldl (fun acc pe => f acc pe.1 pe.2) init) := by
  induction l generalizing init with
  | nil => exact hinit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hp := hl hd (List.mem_cons_self ..)
    have htl := fun pe h => hl pe (List.mem_cons.mpr (Or.inr h))
    rcases hf init hd.1 hd.2 with heq | ⟨v, heq⟩
    · rw [heq]; exact ih init hinit htl
    · rw [heq]
      apply ih
      · intro q hq; rw [Std.TreeMap.mem_insert] at hq
        rcases hq with ⟨hcmp⟩ | hq
        · exact (compare_eq_iff_eq.mp hcmp).symm ▸ hp
        · exact hinit q hq
      · exact htl

/-- Keys from `stateSplit` are a subset of `m`'s keys; hence WF is preserved. -/
theorem stateSplit_wf_fst (thresh m : RegMap) (hwf : RegMap.WF m) :
    RegMap.WF (stateSplit thresh m).fst := by
  unfold stateSplit; dsimp only
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  refine foldl_cond_insert_wf _ _ (fun _ hp => absurd hp Std.TreeMap.not_mem_emptyc) ?_
    (fun acc p e =>
      let t := thresh.getD p 0
      let dataVal := if t = 0 then e else e - min e t
      if dataVal = 0 then acc else acc.insert p dataVal) ?_
  · intro ⟨p, _⟩ hp
    exact hwf p (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp]; rfl))
  · intro acc p e; dsimp only
    by_cases hv : (if thresh.getD p 0 = 0 then e else e - min e (thresh.getD p 0)) = 0
    · left; simp [hv]
    · right; simp [hv]

theorem stateSplit_wf_snd (thresh m : RegMap) (hwf : RegMap.WF m) :
    RegMap.WF (stateSplit thresh m).snd := by
  unfold stateSplit; dsimp only
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  refine foldl_cond_insert_wf _ _ (fun _ hp => absurd hp Std.TreeMap.not_mem_emptyc) ?_
    (fun acc p e =>
      let t := thresh.getD p 0
      if t = 0 then acc
      else
        let logicVal := min e t
        if logicVal = 0 then acc else acc.insert p logicVal) ?_
  · intro ⟨p, _⟩ hp
    exact hwf p (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp]; rfl))
  · intro acc p e; dsimp only
    by_cases ht : thresh.getD p 0 = 0
    · left; simp [ht]
    · simp only [ht, ↓reduceIte]
      by_cases hv : min e (thresh.getD p 0) = 0
      · left; simp [hv]
      · right; simp [hv]

/-- Helper: keys of `m₁.foldl (fun acc p _ => acc.insert p 0) m₂` are
    from `m₁` or `m₂`. -/
private theorem foldl_union_keys_wf (m₁ m₂ : RegMap) (hwf₁ : m₁.WF) (hwf₂ : m₂.WF) :
    (m₁.foldl (fun acc p _ => acc.insert p 0) m₂).WF := by
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  have hl : ∀ pe ∈ m₁.toList, pe.1.Prime :=
    fun pe hp => hwf₁ pe.1 (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp]; rfl))
  exact foldl_cond_insert_wf m₁.toList m₂ hwf₂ hl
    (fun acc p _ => acc.insert p 0) (fun acc p _ => Or.inr ⟨0, rfl⟩)

/-- Helper: foldl over a list of primes, conditionally inserting into a WF map, gives WF. -/
private theorem foldl_keys_insert_wf (keys : List ℕ) (init : RegMap) (hinit : RegMap.WF init)
    (hkeys : ∀ p ∈ keys, p.Prime) (f : RegMap → ℕ → RegMap)
    (hf : ∀ acc p, f acc p = acc ∨ ∃ v, f acc p = acc.insert p v) :
    RegMap.WF (keys.foldl f init) := by
  induction keys generalizing init with
  | nil => exact hinit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hp := hkeys hd (List.mem_cons_self ..)
    have htl := fun p h => hkeys p (List.mem_cons.mpr (Or.inr h))
    rcases hf init hd with heq | ⟨v, heq⟩
    · rw [heq]; exact ih init hinit htl
    · rw [heq]; apply ih _ _ htl
      intro q hq; rw [Std.TreeMap.mem_insert] at hq
      rcases hq with ⟨hcmp⟩ | hq
      · exact (compare_eq_iff_eq.mp hcmp).symm ▸ hp
      · exact hinit q hq

/-- Helper: keys from a WF map's toList are all prime. -/
private theorem toList_map_fst_prime (m : RegMap) (hwf : m.WF) :
    ∀ p ∈ m.toList.map Prod.fst, p.Prime := by
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨⟨k, v⟩, hkv, rfl⟩ := hp
  exact hwf k (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
    rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hkv]; rfl))

/-- Helper: `m₁ * m₂` is WF when both inputs are WF. -/
private theorem mul_wf (m₁ m₂ : RegMap) (hwf₁ : m₁.WF) (hwf₂ : m₂.WF) :
    (m₁ * m₂).WF := by
  change (m₁.foldl (fun acc p e => acc.insert p (acc.get p + e)) m₂).WF
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  have hl : ∀ pe ∈ m₁.toList, pe.1.Prime :=
    fun pe hp => hwf₁ pe.1 (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp]; rfl))
  exact foldl_cond_insert_wf m₁.toList m₂ hwf₂ hl
    (fun acc p e => acc.insert p (acc.get p + e))
    (fun acc p e => Or.inr ⟨acc.get p + e, rfl⟩)

/-- `leapState` preserves well-formedness of register maps. -/
theorem leapState_wf (startData endData logic : RegMap) (c : ℕ)
    (hsd : RegMap.WF startData) (hed : RegMap.WF endData)
    (hl : RegMap.WF logic) :
    RegMap.WF (leapState startData endData logic c) := by
  unfold leapState
  apply mul_wf
  · apply foldl_keys_insert_wf
    · exact fun _ hp => absurd hp Std.TreeMap.not_mem_emptyc
    · exact toList_map_fst_prime _ (foldl_union_keys_wf startData endData hsd hed)
    · intro acc p; dsimp only
      by_cases hv : (if endData.getD p 0 ≥ startData.getD p 0
        then endData.getD p 0 + c * (endData.getD p 0 - startData.getD p 0)
        else endData.getD p 0 - c * (startData.getD p 0 - endData.getD p 0)) = 0
      · left; simp [hv]
      · right; simp [hv]
  · exact hl

/-- If two well-formed RegMaps agree on every register, they have the same unfmap. -/
private theorem unfmap_eq_of_forall_getD (m₁ m₂ : RegMap)
    (h₁ : RegMap.WF m₁) (h₂ : RegMap.WF m₂)
    (h : ∀ p, m₁.getD p 0 = m₂.getD p 0) :
    RegMap.unfmap m₁ = RegMap.unfmap m₂ := by
  apply Nat.factorization_inj (RegMap.unfmap_pos m₁ h₁).ne' (RegMap.unfmap_pos m₂ h₂).ne'
  rw [RegMap.factorization_unfmap_eq_toFinsupp m₁ h₁,
      RegMap.factorization_unfmap_eq_toFinsupp m₂ h₂]
  ext p; simp [h p]

/-- Main leap theorem: factored through helper lemmas.

    Proof outline:
    1. Extract `m_start` from buffer at the cycle's start point
    2. Show `m_start` and `st.m` have same logic state → `CycleInvariant`
    3. Decompose `naiveRun n (s + L*c)` as `naiveRun n s >>= naiveRun · (L*c)`
    4. Apply `iterated_cycle` to get the final state after `c` cycles
    5. Show the final state's unfmap equals `leapState`'s unfmap -/
theorem leap_correct
    (prog : FractranProg) (n : ℕ)
    (hw : prog.WellFormed) (_hn : 0 < n)
    (thresh dmaxes : RegMap) (st : CycleState)
    (hthresh : thresh = dthreshMap prog.toRegProg (st.buf.cap))
    (hdmaxes : dmaxes = dmaxesMap prog.toRegProg)
    (hinv : naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m))
    (hwf : RegMap.WF st.m)
    (hbuf : BufferInvariant prog n thresh st.buf st.stepsSimulated)
    (range : List (RegMap × RegMap))
    (hgr : st.buf.getRange Prod.snd (stateSplit thresh st.m).snd = some range)
    (c : ℕ) (hc : 0 < c)
    (hlc : leapCount dmaxes
      ((stateSplit thresh st.m).fst :: (range.dropLast.map Prod.fst))
      ((range.getLast!).fst) ((stateSplit thresh st.m).fst) = some c) :
    naiveRun prog n (st.stepsSimulated + range.length * c) =
      some (RegMap.unfmap (leapState ((range.getLast!).fst)
        ((stateSplit thresh st.m).fst) ((stateSplit thresh st.m).snd) c)) := by
  -- Step 1: Extract cycle start state from buffer
  set L := range.length
  have hLpos : 0 < L :=
    CBuf.getRange_length_pos st.buf Prod.snd (stateSplit thresh st.m).snd range hgr
  obtain ⟨_, hentries⟩ := hbuf
  -- Find the matching buffer entry (the last element of range)
  have hgr' := hgr
  simp only [CBuf.getRange, Option.map_eq_some_iff] at hgr'
  obtain ⟨idx, hfind, hrange_eq⟩ := hgr'
  have hidx := (List.findIdx?_eq_some_iff_getElem.mp hfind).1
  have hL_eq : L = idx + 1 := by
    change range.length = idx + 1
    rw [← hrange_eq, List.length_take]; omega
  -- Extract m_start
  obtain ⟨m_start, hstart_split, hstart_run, hstart_wf⟩ := hentries idx hidx
  have hstep : st.stepsSimulated - 1 - idx = st.stepsSimulated - L := by omega
  rw [hstep] at hstart_run
  -- Step 2: Show logic states match → CycleInvariant
  -- The findIdx match tells us the logic states are BEq-equal
  have hfind_pred := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
  rw [hstart_split] at hfind_pred
  -- BEq on RegMap compares toList
  have hlogic_toList : (stateSplit thresh m_start).snd.toList =
      (stateSplit thresh st.m).snd.toList := by
    -- hfind_pred : (Prod.snd (stateSplit thresh m_start) == ...) = true
    -- BEq for RegMap compares toList, and List has LawfulBEq
    change ((stateSplit thresh m_start).snd.toList ==
           (stateSplit thresh st.m).snd.toList) = true at hfind_pred
    exact beq_iff_eq.mp hfind_pred
  have hlogic_match : ∀ p, (stateSplit thresh m_start).snd.getD p 0 =
      (stateSplit thresh st.m).snd.getD p 0 :=
    fun p => getD_eq_of_toList_eq _ _ hlogic_toList p 0
  have hthresh_eq : ∀ p, thresh.getD p 0 =
      st.buf.cap * maxDenom prog.toRegProg p := by
    intro p; rw [hthresh]; exact dthreshMap_spec prog.toRegProg st.buf.cap p
  have hcycle_inv : CycleInvariant prog.toRegProg st.buf.cap m_start st.m :=
    stateSplit_implies_cycleInvariant prog.toRegProg st.buf.cap thresh
      m_start st.m hthresh_eq hlogic_match
  -- Step 3: One cycle from m_start reaches st.m
  have hone_cycle : naiveRun prog (RegMap.unfmap m_start) L =
      some (RegMap.unfmap st.m) := by
    have h := naiveRun_add prog n (st.stepsSimulated - L) L
    rw [show st.stepsSimulated - L + L = st.stepsSimulated from by omega] at h
    rw [h, hstart_run] at hinv
    simpa [Option.bind] using hinv
  -- Step 4: Reduce the goal to naiveRun from st.m for L*c steps
  -- naiveRun n (s + L*c) = naiveRun n (s-L) >>= naiveRun · (L + L*c)
  --   = naiveRun (unfmap m_start) (L + L*c)
  --   = naiveRun (unfmap m_start) L >>= naiveRun · (L*c)
  --   = naiveRun (unfmap st.m) (L*c)
  have hgoal_eq : naiveRun prog n (st.stepsSimulated + L * c) =
      naiveRun prog (RegMap.unfmap st.m) (L * c) := by
    have h1 := naiveRun_add prog n (st.stepsSimulated - L) (L + L * c)
    rw [show st.stepsSimulated - L + (L + L * c) = st.stepsSimulated + L * c from by omega] at h1
    rw [h1, hstart_run]
    change naiveRun prog (RegMap.unfmap m_start) (L + L * c) = _
    have h2 := naiveRun_add prog (RegMap.unfmap m_start) L (L * c)
    rw [hone_cycle] at h2
    change naiveRun prog (RegMap.unfmap m_start) (L + L * c) =
      naiveRun prog (RegMap.unfmap st.m) (L * c) at h2
    exact h2
  rw [hgoal_eq]
  -- Step 5: Apply iterated_cycle_per_reg using leapCount-derived per-register safety
  -- First convert hone_cycle (naiveRun) to regRun.
  -- regRun gives some m' with unfmap m' = unfmap st.m, but m' might differ
  -- from st.m structurally; use it via getD equivalence.
  obtain ⟨st_m_alt, hreg_one, hwf_st_m_alt, hgetD_alt⟩ :
      ∃ m', regRun prog.toRegProg m_start L = some m' ∧ m'.WF ∧
            ∀ p, m'.getD p 0 = st.m.getD p 0 := by
    have h := regRun_map_unfmap prog m_start hstart_wf L hw
    rw [hone_cycle] at h
    cases hr : regRun prog.toRegProg m_start L with
    | none => rw [hr] at h; simp only [Option.map_none, reduceCtorEq] at h
    | some m' =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hwf_m' := regRun_wf prog m_start hstart_wf hw L m' hr
      exact ⟨m', rfl, hwf_m', RegMap.getD_eq_of_unfmap_eq m' st.m hwf_m' hwf h⟩
  -- Identify range.getLast! as the matching buffer entry (= stateSplit thresh m_start).
  have hrange_getLast! : range.getLast! = stateSplit thresh m_start := by
    conv_lhs =>
      rw [show range = st.buf.toList.take (idx + 1) from hrange_eq.symm]
    simp only [List.getLast!_eq_getLast?_getD]
    rw [List.getLast?_take]
    rw [if_neg (by omega)]
    rw [show idx + 1 - 1 = idx from by omega,
        List.getElem?_eq_getElem hidx, Option.some_or, Option.getD_some]
    exact hstart_split
  -- Build hsafe for iterated_cycle_per_reg from leapCount safety.
  -- For each register p with delta_full ≠ 0, the trajectory states m_i (for
  -- i < L) are either m_start (i=0) or buffer entries (i ∈ [1, L-1]). Buffer
  -- entries' data parts are in leapCount's history. By leapCount_pos_imp,
  -- minVal ≥ maxDenom; and for decreasing registers, c * (s - e) ≤ minVal -
  -- maxDenom. Combined with stateSplit_recover, m_i_p satisfies the
  -- per-register data_irrelevant preconditions.
  have hdmaxes_p : ∀ p, dmaxes.getD p 0 = maxDenom prog.toRegProg p := by
    intro p; rw [hdmaxes]; exact dmaxesMap_spec prog.toRegProg p
  have hcap_pos : 0 < st.buf.cap := st.buf.hCapPos
  have hsafe : ∀ i, i < L → ∀ m_i, RegMap.WF m_i →
                regRun prog.toRegProg m_start i = some m_i →
                ∀ p, (m_i.getD p 0 < maxDenom prog.toRegProg p →
                        (c : ℤ) * ((st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ)) = 0) ∧
                     (m_i.getD p 0 ≥ maxDenom prog.toRegProg p →
                        (m_i.getD p 0 : ℤ) +
                          (c : ℤ) * ((st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ)) ≥
                        maxDenom prog.toRegProg p) := by
    intro i hi m_i hwf_mi hrun_mi p
    -- Convert delta to use st.m instead of st_m_alt
    have hgetD := hgetD_alt p
    have hdelta_st : (st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ) =
                     (st.m.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ) := by
      have : (st_m_alt.getD p 0 : ℤ) = (st.m.getD p 0 : ℤ) := by exact_mod_cast hgetD
      omega
    -- Case split on delta = 0
    by_cases hd_zero : st.m.getD p 0 = m_start.getD p 0
    · -- delta = 0: both clauses trivial
      have hdelta_zero : (st_m_alt.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ) = 0 := by
        rw [hdelta_st]
        have : (st.m.getD p 0 : ℤ) = (m_start.getD p 0 : ℤ) := by exact_mod_cast hd_zero
        omega
      refine ⟨?_, ?_⟩
      · intro _; rw [hdelta_zero]; ring
      · intro hp; rw [hdelta_zero]; linarith
    · -- delta ≠ 0: use CycleInvariant branch (b)
      have hbr : m_start.getD p 0 ≥ st.buf.cap * maxDenom prog.toRegProg p ∧
                 st.m.getD p 0 ≥ st.buf.cap * maxDenom prog.toRegProg p := by
        rcases hcycle_inv p with h | h
        · exact absurd h.symm hd_zero
        · exact h
      -- State decomposition via stateSplit_recover
      have hs_decomp : m_start.getD p 0 =
          (stateSplit thresh m_start).fst.getD p 0 +
          (stateSplit thresh m_start).snd.getD p 0 := by
        have hrec := stateSplit_recover thresh m_start p
        simp only [] at hrec
        rw [RegMap.mul_getD] at hrec; linarith
      have he_decomp : st.m.getD p 0 =
          (stateSplit thresh st.m).fst.getD p 0 +
          (stateSplit thresh st.m).snd.getD p 0 := by
        have hrec := stateSplit_recover thresh st.m p
        simp only [] at hrec
        rw [RegMap.mul_getD] at hrec; linarith
      have hlg : (stateSplit thresh m_start).snd.getD p 0 =
                 (stateSplit thresh st.m).snd.getD p 0 := hlogic_match p
      have hd_data_ne : (stateSplit thresh m_start).fst.getD p 0 ≠
                        (stateSplit thresh st.m).fst.getD p 0 := by
        intro h; apply hd_zero
        rw [he_decomp, ← h, ← hlg, ← hs_decomp]
      -- p is in the keys list of leapCount
      have hsd_eq_split : (range.getLast!).fst = (stateSplit thresh m_start).fst := by
        rw [hrange_getLast!]
      have hp_in_keys : p ∈ ((range.getLast!).fst.foldl
          (fun acc q _ => acc.insert q 0) (stateSplit thresh st.m).fst).toList.map Prod.fst := by
        rw [Std.TreeMap.map_fst_toList_eq_keys, Std.TreeMap.mem_keys,
            Std.TreeMap.foldl_eq_foldl_toList]
        apply mem_list_foldl_insert
        by_cases hs_pos : (stateSplit thresh m_start).fst.getD p 0 > 0
        · right
          rw [Std.TreeMap.map_fst_toList_eq_keys, Std.TreeMap.mem_keys, hsd_eq_split]
          by_contra hp_not
          rw [Std.TreeMap.getD_eq_fallback hp_not] at hs_pos
          omega
        · push Not at hs_pos
          have hs_zero : (stateSplit thresh m_start).fst.getD p 0 = 0 := Nat.le_zero.mp hs_pos
          have he_pos : (stateSplit thresh st.m).fst.getD p 0 > 0 := by
            have := hd_data_ne; omega
          left
          by_contra hp_not
          rw [Std.TreeMap.getD_eq_fallback hp_not] at he_pos
          omega
      -- Apply leapCount_pos_imp
      have hlc_p := leapCount_pos_imp dmaxes
        ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst)
        (range.getLast!).fst (stateSplit thresh st.m).fst c hc hlc p hp_in_keys
      -- Simplify s, e, minVal at the type level
      simp only [hsd_eq_split] at hlc_p
      set s_data := (stateSplit thresh m_start).fst.getD p 0 with hs_data_def
      set e_data := (stateSplit thresh st.m).fst.getD p 0 with he_data_def
      set lg := (stateSplit thresh st.m).snd.getD p 0 with hlg_def
      have hs_full : m_start.getD p 0 = s_data + lg := by rw [hs_decomp, hlg]
      have he_full : st.m.getD p 0 = e_data + lg := he_decomp
      -- minVal definition
      set minVal := ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst).foldl
                      (fun acc m => min acc (m.getD p 0))
                      (((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst).head!.getD p 0)
                    with hminVal_def
      -- minVal ≤ e_data (e_data is the head value)
      have hmin_le_e : minVal ≤ e_data := by
        rw [hminVal_def]
        change (((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst).foldl
                  (fun acc m => min acc (m.getD p 0))
                  ((stateSplit thresh st.m).fst.getD p 0)) ≤ e_data
        exact foldl_min_proj_le_init _ _ _
      -- s_data > e_data branch will need: c * (s_data - e_data) ≤ minVal - maxDenom_p
      -- s_data ≠ e_data branch will need: minVal ≥ maxDenom_p
      have hbound_eq : minVal ≥ maxDenom prog.toRegProg p := by
        have h := hlc_p.1 hd_data_ne
        rw [hdmaxes_p] at h
        exact h
      have hbound_gt : s_data > e_data →
          c * (s_data - e_data) ≤ minVal - maxDenom prog.toRegProg p := by
        intro hgt
        have h := hlc_p.2 hgt
        rw [hdmaxes_p] at h
        exact h
      -- range.dropLast equals buf.toList.take idx
      have hdropLast : range.dropLast = st.buf.toList.take idx := by
        rw [show range = st.buf.toList.take (idx + 1) from hrange_eq.symm,
            List.dropLast_eq_take, List.length_take,
            show min (idx + 1) st.buf.toList.length = idx + 1 from
              Nat.min_eq_left (by omega), List.take_take,
            show min (idx + 1 - 1) (idx + 1) = idx from by omega]
      -- For i ≥ 1: derive m_i.getD p 0 ≥ minVal via buffer entry analysis.
      -- The result m_i_ge: m_i.getD p 0 ≥ maxDenom_p (when i ≥ 1).
      have hi_ge_maxDenom : i ≥ 1 → m_i.getD p 0 ≥ maxDenom prog.toRegProg p := by
        intro hi_pos
        -- Buffer index for m_i is j = L - 1 - i = idx - i
        set j := idx - i with hj_def
        have hj_lt_idx : j < idx := by omega
        have hj_lt_buf : j < st.buf.toList.length := by omega
        -- Extract buffer entry
        obtain ⟨m_buf_j, hbuf_split, hbuf_run, hbuf_wf⟩ := hentries j hj_lt_buf
        -- naiveRun reaches the same state as our regRun trajectory
        have hsteps_eq : st.stepsSimulated - 1 - j = st.stepsSimulated - L + i := by omega
        rw [hsteps_eq] at hbuf_run
        -- Trajectory: naiveRun n (stepsSimulated - L + i) = naiveRun (unfmap m_start) i
        have hnr_split : naiveRun prog n (st.stepsSimulated - L + i) =
            naiveRun prog (RegMap.unfmap m_start) i := by
          rw [naiveRun_add, hstart_run]; rfl
        -- regRun → naiveRun via regRun_map_unfmap
        have hreg_to_naive : naiveRun prog (RegMap.unfmap m_start) i =
            some (RegMap.unfmap m_i) := by
          have h := regRun_map_unfmap prog m_start hstart_wf i hw
          rw [hrun_mi] at h; exact h.symm
        -- Combine via transitivity through naiveRun n (stepsSimulated - L + i)
        have heq_unfmap : RegMap.unfmap m_i = RegMap.unfmap m_buf_j := by
          have htrans : some (RegMap.unfmap m_i) = some (RegMap.unfmap m_buf_j) := by
            rw [← hreg_to_naive, ← hnr_split]; exact hbuf_run
          exact Option.some.inj htrans
        have hgetD_eq : m_i.getD p 0 = m_buf_j.getD p 0 :=
          RegMap.getD_eq_of_unfmap_eq m_i m_buf_j hwf_mi hbuf_wf heq_unfmap p
        -- m_buf_j.getD p 0 ≥ data part = (stateSplit thresh m_buf_j).fst.getD p 0
        have hdata_le : (stateSplit thresh m_buf_j).fst.getD p 0 ≤ m_buf_j.getD p 0 := by
          rw [stateSplit_data_getD]
          split_ifs <;> omega
        -- (stateSplit thresh m_buf_j).fst is in range.dropLast.map Prod.fst
        have hbuf_in_range : (stateSplit thresh m_buf_j).fst ∈ range.dropLast.map Prod.fst := by
          rw [hdropLast]
          rw [← hbuf_split]
          apply List.mem_map.mpr
          refine ⟨st.buf.toList[j], ?_, rfl⟩
          exact List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
        -- (stateSplit thresh m_buf_j).fst is in history (right of cons)
        have hbuf_in_hist :
            (stateSplit thresh m_buf_j).fst ∈
            (stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst :=
          List.mem_cons.mpr (Or.inr hbuf_in_range)
        -- minVal ≤ data of m_buf_j
        have hmin_le_buf : minVal ≤ (stateSplit thresh m_buf_j).fst.getD p 0 := by
          rw [hminVal_def]
          exact foldl_min_proj_le_mem _ _ _ _ hbuf_in_hist
        -- Combine: m_i.getD p 0 ≥ minVal ≥ maxDenom_p
        omega
      -- Now prove both parts
      refine ⟨?_, ?_⟩
      · -- Part 1: m_i_p < maxDenom_p → c * delta = 0
        intro hp
        rw [hdelta_st]
        -- Derive contradiction
        exfalso
        rcases Nat.eq_zero_or_pos i with hi_zero | hi_pos
        · -- i = 0: m_i = m_start
          have hi_eq : m_i = m_start := by
            simp only [regRun, hi_zero] at hrun_mi
            exact (Option.some.inj hrun_mi).symm
          rw [hi_eq] at hp
          -- m_start_p ≥ cap * maxDenom_p ≥ maxDenom_p (cap ≥ 1)
          -- When maxDenom_p = 0: hp : m_start_p < 0, impossible.
          -- When maxDenom_p > 0: m_start_p ≥ maxDenom_p, contradicts hp.
          have h1 := hbr.1
          have hmd_pos : 0 < maxDenom prog.toRegProg p := by
            by_contra h; push Not at h
            have : maxDenom prog.toRegProg p = 0 := Nat.le_zero.mp h
            omega
          have : m_start.getD p 0 ≥ maxDenom prog.toRegProg p := by
            calc m_start.getD p 0 ≥ st.buf.cap * maxDenom prog.toRegProg p := h1
              _ ≥ 1 * maxDenom prog.toRegProg p :=
                Nat.mul_le_mul_right _ hcap_pos
              _ = maxDenom prog.toRegProg p := one_mul _
          omega
        · -- i ≥ 1: use hi_ge_maxDenom
          have := hi_ge_maxDenom hi_pos
          omega
      · -- Part 2: m_i_p ≥ maxDenom_p → m_i_p + c*delta ≥ maxDenom_p
        intro hp
        rw [hdelta_st]
        -- delta = e_full - s_full = e_data - s_data (since logic cancels)
        have hdelta_data : (st.m.getD p 0 : ℤ) - (m_start.getD p 0 : ℤ) =
                           (e_data : ℤ) - (s_data : ℤ) := by
          rw [he_full, hs_full]; push_cast; ring
        rw [hdelta_data]
        -- Case on sign of delta
        by_cases hdelta_sign : e_data ≥ s_data
        · -- delta ≥ 0: m_i + c*delta ≥ m_i ≥ maxDenom_p
          have hdelta_nn : (0 : ℤ) ≤ (e_data : ℤ) - (s_data : ℤ) := by
            omega
          have : (c : ℤ) * ((e_data : ℤ) - (s_data : ℤ)) ≥ 0 := by positivity
          linarith
        · -- delta < 0: harder case
          push Not at hdelta_sign
          have hsd_gt : s_data > e_data := hdelta_sign
          have hcb := hbound_gt hsd_gt
          -- hcb : c * (s_data - e_data) ≤ minVal - maxDenom_p (in ℕ)
          have hsub_le : e_data ≤ s_data := le_of_lt hsd_gt
          have hmin_ge : maxDenom prog.toRegProg p ≤ minVal := hbound_eq
          -- Convert to ℤ
          have hcb_int : (c : ℤ) * ((s_data : ℤ) - (e_data : ℤ)) ≤
                         (minVal : ℤ) - (maxDenom prog.toRegProg p : ℤ) := by
            have hcb_cast : ((c * (s_data - e_data) : ℕ) : ℤ) ≤
                            ((minVal - maxDenom prog.toRegProg p : ℕ) : ℤ) := by
              exact_mod_cast hcb
            push_cast [Nat.cast_sub hsub_le, Nat.cast_sub hmin_ge] at hcb_cast
            linarith
          -- m_i_p + c*(e_data - s_data) = m_i_p - c*(s_data - e_data)
          -- ≥ m_i_p - (minVal - maxDenom_p)
          -- For i = 0: m_i_p = s_data + lg ≥ s_data > e_data ≥ minVal, so ≥ minVal
          -- For i ≥ 1: m_i_p ≥ minVal directly
          rcases Nat.eq_zero_or_pos i with hi_zero | hi_pos
          · -- i = 0: m_i = m_start, so m_i_p = s_data + lg
            have hi_eq : m_i = m_start := by
              simp only [regRun, hi_zero] at hrun_mi
              exact (Option.some.inj hrun_mi).symm
            have hmip : m_i.getD p 0 = s_data + lg := by rw [hi_eq, hs_full]
            -- Goal: (s_data + lg : ℤ) + c * (e_data - s_data) ≥ maxDenom_p
            -- ≥ s_data + lg - (minVal - maxDenom_p) ≥ s_data + lg - (e_data - maxDenom_p)
            -- = (s_data - e_data) + lg + maxDenom_p ≥ maxDenom_p (since s_data > e_data, lg ≥ 0)
            have : (m_i.getD p 0 : ℤ) + (c : ℤ) * ((e_data : ℤ) - (s_data : ℤ)) ≥
                   (maxDenom prog.toRegProg p : ℤ) := by
              rw [hmip]; push_cast
              have hmul : (c : ℤ) * ((e_data : ℤ) - (s_data : ℤ)) =
                          - ((c : ℤ) * ((s_data : ℤ) - (e_data : ℤ))) := by ring
              rw [hmul]
              have hsub_pos_int : (s_data : ℤ) - (e_data : ℤ) > 0 := by omega
              linarith [hmin_le_e]
            exact this
          · -- i ≥ 1: m_i_p ≥ minVal
            -- We have m_i.getD p 0 ≥ maxDenom_p (from hi_ge_maxDenom)
            -- but we need m_i.getD p 0 ≥ minVal for the bound to work
            -- Re-derive: m_i_p ≥ data of m_buf_j ≥ minVal
            have hmi_ge_min : m_i.getD p 0 ≥ minVal := by
              -- Repeat the buffer extraction
              set j := idx - i with hj_def'
              have hj_lt_idx' : j < idx := by omega
              have hj_lt_buf' : j < st.buf.toList.length := by omega
              obtain ⟨m_buf_j, hbuf_split', hbuf_run', hbuf_wf'⟩ := hentries j hj_lt_buf'
              have hsteps_eq' : st.stepsSimulated - 1 - j = st.stepsSimulated - L + i := by omega
              rw [hsteps_eq'] at hbuf_run'
              have hnr_split' : naiveRun prog n (st.stepsSimulated - L + i) =
                  naiveRun prog (RegMap.unfmap m_start) i := by
                rw [naiveRun_add, hstart_run]; rfl
              have hreg_to_naive' : naiveRun prog (RegMap.unfmap m_start) i =
                  some (RegMap.unfmap m_i) := by
                have h := regRun_map_unfmap prog m_start hstart_wf i hw
                rw [hrun_mi] at h; exact h.symm
              have heq_unfmap' : RegMap.unfmap m_i = RegMap.unfmap m_buf_j := by
                have htrans : some (RegMap.unfmap m_i) = some (RegMap.unfmap m_buf_j) := by
                  rw [← hreg_to_naive', ← hnr_split']; exact hbuf_run'
                exact Option.some.inj htrans
              have hgetD_eq' : m_i.getD p 0 = m_buf_j.getD p 0 :=
                RegMap.getD_eq_of_unfmap_eq m_i m_buf_j hwf_mi hbuf_wf' heq_unfmap' p
              have hdata_le' : (stateSplit thresh m_buf_j).fst.getD p 0 ≤ m_buf_j.getD p 0 := by
                rw [stateSplit_data_getD]
                split_ifs <;> omega
              have hbuf_in_range' :
                  (stateSplit thresh m_buf_j).fst ∈ range.dropLast.map Prod.fst := by
                rw [hdropLast]
                apply List.mem_map.mpr
                refine ⟨st.buf.toList[j], ?_, ?_⟩
                · exact List.mem_take_iff_getElem.mpr ⟨j, by omega, rfl⟩
                · exact congr_arg Prod.fst hbuf_split'
              have hbuf_in_hist' :
                  (stateSplit thresh m_buf_j).fst ∈
                  (stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst :=
                List.mem_cons.mpr (Or.inr hbuf_in_range')
              have hmin_le_buf' : minVal ≤ (stateSplit thresh m_buf_j).fst.getD p 0 := by
                rw [hminVal_def]
                exact foldl_min_proj_le_mem _ _ _ _ hbuf_in_hist'
              omega
            -- Now: m_i_p + c*(e_data - s_data) ≥ minVal - (minVal - maxDenom_p) = maxDenom_p
            have hmul : (c : ℤ) * ((e_data : ℤ) - (s_data : ℤ)) =
                        - ((c : ℤ) * ((s_data : ℤ) - (e_data : ℤ))) := by ring
            rw [hmul]
            have : (m_i.getD p 0 : ℤ) ≥ (minVal : ℤ) := by exact_mod_cast hmi_ge_min
            linarith
  obtain ⟨m_final, hreg_final, hwf_final, hdiff_final⟩ :=
    iterated_cycle_per_reg prog hw m_start st_m_alt L hstart_wf hwf_st_m_alt hreg_one c hsafe
  -- Convert back to naiveRun
  have hnaive_final : naiveRun prog (RegMap.unfmap m_start) (L * (c + 1)) =
      some (RegMap.unfmap m_final) := by
    have h := regRun_map_unfmap prog m_start hstart_wf (L * (c + 1)) hw
    rw [hreg_final] at h; simpa using h.symm
  -- Connect: naiveRun from m_start for L*(c+1) = naiveRun from st.m for L*c
  have hrun_from_stm : naiveRun prog (RegMap.unfmap st.m) (L * c) =
      some (RegMap.unfmap m_final) := by
    have h := naiveRun_add prog (RegMap.unfmap m_start) L (L * c)
    rw [hone_cycle] at h
    change naiveRun prog (RegMap.unfmap m_start) (L + L * c) =
      naiveRun prog (RegMap.unfmap st.m) (L * c) at h
    rw [show L + L * c = L * (c + 1) from by ring] at h
    rw [← h]; exact hnaive_final
  rw [hrun_from_stm]; congr 1
  -- Step 6: Show unfmap m_final = unfmap (leapState ...)
  -- Decompose m_start and st.m via stateSplit_recover
  set startData := (range.getLast!).fst
  set endData := (stateSplit thresh st.m).fst
  set logic := (stateSplit thresh st.m).snd
  have hsd_eq : startData = (stateSplit thresh m_start).fst := by
    simp only [startData, hrange_getLast!]
  have hrecover_start : ∀ p, m_start.getD p 0 =
      (stateSplit thresh m_start).fst.getD p 0 +
      (stateSplit thresh m_start).snd.getD p 0 := by
    intro p
    have hmul := RegMap.mul_getD (stateSplit thresh m_start).fst
      (stateSplit thresh m_start).snd p
    have hrec := stateSplit_recover thresh m_start p
    -- hrec (definitionally): (fst * snd).getD p 0 = m_start.getD p 0
    -- hmul: (fst * snd).getD p 0 = fst.getD p 0 + snd.getD p 0
    linarith
  have hrecover_end : ∀ p, st.m.getD p 0 = endData.getD p 0 + logic.getD p 0 := by
    intro p
    have hmul := RegMap.mul_getD (stateSplit thresh st.m).fst
      (stateSplit thresh st.m).snd p
    have hrec := stateSplit_recover thresh st.m p
    linarith
  have hlogic_eq : ∀ p, (stateSplit thresh m_start).snd.getD p 0 = logic.getD p 0 :=
    hlogic_match
  -- Show per-register equality between m_final and leapState
  apply unfmap_eq_of_forall_getD _ _ hwf_final
  · -- leapState = newData * logic; both components are WF
    exact leapState_wf _ _ _ c
      (by rw [hsd_eq]; exact stateSplit_wf_fst thresh m_start hstart_wf)
      (stateSplit_wf_fst thresh st.m hwf)
      (stateSplit_wf_snd thresh st.m hwf)
  · intro p
    have hfinal := hdiff_final p
    -- Convert st_m_alt's getD to st.m's getD via hgetD_alt
    rw [show (st_m_alt.getD p 0 : ℤ) = (st.m.getD p 0 : ℤ) from by
          exact_mod_cast hgetD_alt p] at hfinal
    rw [leapState_spec, hsd_eq]
    -- Substitute decompositions into the ℤ formula from iterated_cycle
    have hstart_decomp := hrecover_start p
    have hend_decomp := hrecover_end p
    have hlogic_p := hlogic_eq p
    rw [hstart_decomp, hlogic_p, hend_decomp] at hfinal
    -- hfinal in ℤ: m_final_p = (sd + lg) + (c+1) * ((ed + lg) - (sd + lg))
    --            = sd + (c+1)*(ed - sd) + lg
    -- After substitution, hfinal says (in ℤ):
    -- m_final_p = (sd + lg) + (c+1) * ((ed + lg) - (sd + lg))
    --           = (c+1)*ed - c*sd + lg
    -- where sd, ed, lg are ℕ values of data/logic parts
    by_cases hed : (stateSplit thresh m_start).fst.getD p 0 ≤ endData.getD p 0
    · -- Increasing/constant case: leapState gives ed + c*(ed - sd) + lg
      simp only [hed, ↓reduceIte]
      -- Both sides cast to the same ℤ value
      have hlhs : (↑(endData.getD p 0 + c * (endData.getD p 0 -
          (stateSplit thresh m_start).fst.getD p 0) + logic.getD p 0) : ℤ) =
          (↑(m_final.getD p 0) : ℤ) := by
        push_cast [Nat.cast_sub hed] at hfinal ⊢; linarith
      exact Int.ofNat_inj.mp hlhs.symm
    · -- Decreasing case: leapState gives ed - c*(sd - ed) + lg
      push Not at hed
      simp only [show ¬((stateSplit thresh m_start).fst.getD p 0 ≤ endData.getD p 0)
        from by omega, ↓reduceIte]
      have hno_underflow : c * ((stateSplit thresh m_start).fst.getD p 0 -
          endData.getD p 0) ≤ endData.getD p 0 := by
        -- sd > ed ≥ 0 (from hed) implies sd > 0, so p ∈ (range.getLast!).fst (TreeMap)
        have hsd_pos : (range.getLast!).fst.getD p 0 > 0 := by
          rw [hrange_getLast!]; exact lt_of_le_of_lt (Nat.zero_le _) hed
        have hp_in_sd_map : p ∈ (range.getLast!).fst := by
          by_contra hpnotin
          rw [Std.TreeMap.getD_eq_fallback hpnotin] at hsd_pos
          omega
        -- p ∈ keys list for leapCount_pos_imp
        have hp_in_keys : p ∈ ((range.getLast!).fst.foldl
            (fun acc q _ => acc.insert q 0) (stateSplit thresh st.m).fst).toList.map Prod.fst := by
          rw [Std.TreeMap.map_fst_toList_eq_keys, Std.TreeMap.mem_keys]
          rw [Std.TreeMap.foldl_eq_foldl_toList]
          apply mem_list_foldl_insert
          right
          rw [Std.TreeMap.map_fst_toList_eq_keys]
          exact Std.TreeMap.mem_keys.mpr hp_in_sd_map
        -- Apply leapCount_pos_imp
        have hlc_p := leapCount_pos_imp dmaxes
          ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst)
          (range.getLast!).fst (stateSplit thresh st.m).fst c hc hlc p hp_in_keys
        -- s = (range.getLast!).fst.getD p 0 = (stateSplit thresh m_start).fst.getD p 0
        -- e = (stateSplit thresh st.m).fst.getD p 0 = endData.getD p 0
        have hs_eq : (range.getLast!).fst.getD p 0 = (stateSplit thresh m_start).fst.getD p 0 := by
          rw [hrange_getLast!]
        have hs_gt_e : (range.getLast!).fst.getD p 0 > (stateSplit thresh st.m).fst.getD p 0 := by
          rw [hs_eq]; exact hed
        have hbound := hlc_p.2 hs_gt_e
        -- minVal ≤ history.head!.getD p 0 = (stateSplit thresh st.m).fst.getD p 0
        have hhead :
            ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst).head!.getD p 0 =
            (stateSplit thresh st.m).fst.getD p 0 := rfl
        have hminVal_le :
            ((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst).foldl
              (fun acc m => min acc (m.getD p 0))
              (((stateSplit thresh st.m).fst :: range.dropLast.map Prod.fst).head!.getD p 0) ≤
            (stateSplit thresh st.m).fst.getD p 0 := by
          rw [hhead]
          exact foldl_min_proj_le_init _ _ _
        -- dmaxes is non-negative (always true for Nat)
        rw [hs_eq] at hbound
        -- hbound : c * (sd - ed) ≤ minVal - dmaxes.getD p 0
        -- minVal ≤ ed, so minVal - dmaxes ≤ ed
        -- endData = (stateSplit thresh st.m).fst by `set`
        change c * ((stateSplit thresh m_start).fst.getD p 0 -
            (stateSplit thresh st.m).fst.getD p 0) ≤ (stateSplit thresh st.m).fst.getD p 0
        omega
      have hed_le_sd : endData.getD p 0 ≤ (stateSplit thresh m_start).fst.getD p 0 := by omega
      have hlhs : (↑(endData.getD p 0 - c * ((stateSplit thresh m_start).fst.getD p 0 -
          endData.getD p 0) + logic.getD p 0) : ℤ) =
          (↑(m_final.getD p 0) : ℤ) := by
        push_cast [Nat.cast_sub hno_underflow, Nat.cast_sub hed_le_sd] at hfinal ⊢; linarith
      exact Int.ofNat_inj.mp hlhs.symm

/-- Any element of the buffer has a WF `.fst` component, since the buffer
    invariant guarantees each entry is `stateSplit thresh m_i` for some WF `m_i`. -/
theorem bufferInvariant_fst_wf (prog : FractranProg) (n : ℕ) (thresh : RegMap)
    (buf : CBuf (RegMap × RegMap)) (stepsSimulated : ℕ)
    (hbuf : BufferInvariant prog n thresh buf stepsSimulated)
    (x : RegMap × RegMap) (hx : x ∈ buf.toList) :
    RegMap.WF x.fst := by
  obtain ⟨_, hentries⟩ := hbuf
  rw [List.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨m_i, heq, _, hwf_i⟩ := hentries i hi
  rw [heq]
  exact stateSplit_wf_fst thresh m_i hwf_i

/-- One step of the cycle-detecting interpreter.
    Consumes one fuel unit: either detects a cycle and leaps, or takes one
    normal elimination step. If the program halts (no fraction applies),
    sets `halted := true`. -/
def cycleStep (table : Array (List Candidate))
    (fallback : List Candidate)
    (thresh dmaxes : RegMap)
    (st : CycleState) : CycleState :=
  if st.halted then st
  else
  -- 1. Split current state into (data, logic) components
  let state := stateSplit thresh st.m
  -- 2. Check if the logic state was seen before in the buffer
  match st.buf.getRange Prod.snd state.snd with
  | some range =>
    -- Cycle detected! range is newest-first, match is last element.
    let startData := (range.getLast!).fst  -- matching (oldest) entry's data
    let endData := state.fst               -- current state's data
    -- history: current data + intermediate datas (excluding the match)
    let history := endData :: (range.dropLast.map Prod.fst)
    let c := match leapCount dmaxes history startData endData with
      | some c => c
      | none => 0  -- nonterminating cycle or can't compute, treat as c=0
    if c = 0 then
      -- Can't safely leap; reset buffer and do a normal step
      match elimStep st.cands st.m with
      | none => { st with halted := true }
      | some (i, m') =>
        let nextCands := if h : i < table.size then table[i] else fallback
        { m := m', cands := nextCands,
          buf := CBuf.empty st.buf.cap st.buf.hCapPos,
          stepsSimulated := st.stepsSimulated + 1 }
    else
      -- Leap forward by c cycle repetitions
      let newM := leapState startData endData state.snd c
      { m := newM, cands := fallback,
        buf := CBuf.empty st.buf.cap st.buf.hCapPos,
        stepsSimulated := st.stepsSimulated + range.length * c }
  | none =>
    -- No cycle detected, do a normal elimination step
    match elimStep st.cands st.m with
    | none => { st with halted := true }
    | some (i, m') =>
      let nextCands := if h : i < table.size then table[i] else fallback
      { m := m', cands := nextCands,
        buf := st.buf.insert state,
        stepsSimulated := st.stepsSimulated + 1 }

/-- Iterate `cycleStep` for `fuel` steps. Tail-recursive. -/
def cycleRunAux (table : Array (List Candidate))
    (fallback : List Candidate)
    (thresh dmaxes : RegMap) :
    CycleState → ℕ → CycleState
  | st, 0 => st
  | st, fuel + 1 =>
    cycleRunAux table fallback thresh dmaxes
      (cycleStep table fallback thresh dmaxes st) fuel

/-- Nat-level cycle-detecting interpreter conforming to the `Correct` interface.
    When still running, the simulated step count `j` may exceed `k` (because leaps
    simulate multiple naive steps). When halted, `j` is the exact number of
    successful naive steps before halting (so `j` may be less than `k`). -/
def cycleRunNat (cyclen : ℕ) (hcyclen : 0 < cyclen)
    (prog : FractranProg) (n k : ℕ) : Option ℕ × ℕ :=
  let regProg := prog.toRegProg
  let table := optTable regProg
  let cands := allCandidates regProg
  let thresh := dthreshMap regProg cyclen
  let dmaxes := dmaxesMap regProg
  let initState : CycleState :=
    { m := RegMap.facmap n
      cands := cands
      buf := CBuf.empty cyclen hcyclen
      stepsSimulated := 0 }
  let result := cycleRunAux table cands thresh dmaxes initState k
  if result.halted then
    (none, result.stepsSimulated)
  else
    (some (RegMap.unfmap result.m), result.stepsSimulated)

/-! ## Top-level correctness -/

/-- Once `naiveRun` returns `none` (halted), it stays `none` for all later steps. -/
theorem naiveRun_none_of_ge (prog : FractranProg) (n : ℕ) {k j : ℕ}
    (hkj : k ≤ j) (hk : naiveRun prog n k = none) :
    naiveRun prog n j = none := by
  induction j with
  | zero => exact Nat.le_zero.mp hkj ▸ hk
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
    · exact hk
    · have h := ih (Nat.lt_succ_iff.mp hlt)
      change naiveRun prog n j >>= naiveStep prog = none
      rw [h]; rfl

/-- `naiveRun` at step `k+1` is `none` when the program halts at step `k`:
    i.e., `naiveRun` at `k` gives `some m` and `naiveStep m = none`. -/
theorem naiveRun_succ_none (prog : FractranProg) (n : ℕ) (k : ℕ) (m : ℕ)
    (hrun : naiveRun prog n k = some m) (hstep : naiveStep prog m = none) :
    naiveRun prog n (k + 1) = none := by
  unfold naiveRun; rw [hrun]; exact hstep

/-- One step either halts or increments `stepsSimulated` by at least 1. -/
theorem cycleStep_progress
    (table : Array (List Candidate)) (fallback : List Candidate)
    (thresh dmaxes : RegMap) (st : CycleState) :
    let st' := cycleStep table fallback thresh dmaxes st
    st'.halted ∨ st'.stepsSimulated ≥ st.stepsSimulated + 1 := by
  change (cycleStep table fallback thresh dmaxes st).halted ∨
       (cycleStep table fallback thresh dmaxes st).stepsSimulated ≥ st.stepsSimulated + 1
  unfold cycleStep
  cases hh : st.halted
  · -- st.halted = false
    simp only [Bool.false_eq_true, ↓reduceIte]
    match hgr : st.buf.getRange Prod.snd (stateSplit thresh st.m).snd with
    | none =>
      match hes : elimStep st.cands st.m with
      | none => simp_all
      | some (i, m') => simp_all
    | some range =>
      match hlc : leapCount dmaxes
          ((stateSplit thresh st.m).fst :: (range.dropLast.map Prod.fst))
          ((range.getLast!).fst) ((stateSplit thresh st.m).fst) with
      | none =>
        match hes : elimStep st.cands st.m with
        | none => simp_all
        | some (i, m') => simp_all
      | some c =>
        by_cases hc : c = 0
        · match hes : elimStep st.cands st.m with
          | none => simp_all
          | some (i, m') => simp_all
        · -- leap case: c > 0
          have hlen : 0 < range.length := CBuf.getRange_length_pos _ _ _ _ hgr
          have hcpos : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc
          have hmul : 1 ≤ range.length * c :=
            one_le_mul_of_one_le_of_one_le (by omega) hcpos
          simp_all
  · -- st.halted = true
    left; simp [hh]

/-- `cycleStep` preserves buffer capacity. -/
@[simp] theorem cycleStep_preserves_cap
    (table : Array (List Candidate)) (fallback : List Candidate)
    (thresh dmaxes : RegMap) (st : CycleState) :
    (cycleStep table fallback thresh dmaxes st).buf.cap = st.buf.cap := by
  unfold cycleStep
  cases st.halted <;> (simp only [Bool.false_eq_true, ↓reduceIte]; try rfl)
  match st.buf.getRange Prod.snd (stateSplit thresh st.m).snd with
  | none =>
    dsimp only
    match elimStep st.cands st.m with
    | none => rfl
    | some (_, _) => simp [CBuf.cap_insert]
  | some range =>
    dsimp only
    match leapCount dmaxes ((stateSplit thresh st.m).fst :: (range.dropLast.map Prod.fst))
        ((range.getLast!).fst) ((stateSplit thresh st.m).fst) with
    | none =>
      dsimp only
      match elimStep st.cands st.m with
      | none => rfl
      | some (_, _) => simp [CBuf.cap_empty]
    | some c =>
      dsimp only
      by_cases hc : c = 0 <;> simp only [hc, ↓reduceIte]
      · match elimStep st.cands st.m with
        | none => rfl
        | some (_, _) => simp [CBuf.cap_empty]
      · simp [CBuf.cap_empty]

/-- A halted state stays halted through `cycleStep`. -/
theorem cycleStep_halted_stable
    (table : Array (List Candidate)) (fallback : List Candidate)
    (thresh dmaxes : RegMap) (st : CycleState) (hh : st.halted) :
    (cycleStep table fallback thresh dmaxes st).halted := by
  simp [cycleStep, hh]

/-- `cycleRunAux` preserves halted state: if the input is halted, the output is halted. -/
theorem cycleRunAux_halted_stable
    (table : Array (List Candidate)) (fallback : List Candidate)
    (thresh dmaxes : RegMap) (st : CycleState) (fuel : ℕ) (hh : st.halted) :
    (cycleRunAux table fallback thresh dmaxes st fuel).halted := by
  induction fuel generalizing st with
  | zero => simp [cycleRunAux, hh]
  | succ fuel ih =>
    simp only [cycleRunAux]
    exact ih _ (cycleStep_halted_stable table fallback thresh dmaxes st hh)

theorem cycleRunAux_stepsSimulated_ge
    (table : Array (List Candidate)) (fallback : List Candidate)
    (thresh dmaxes : RegMap) (st : CycleState) (fuel : ℕ) :
    let result := cycleRunAux table fallback thresh dmaxes st fuel
    result.halted ∨ result.stepsSimulated ≥ st.stepsSimulated + fuel := by
  induction fuel generalizing st with
  | zero => right; simp [cycleRunAux]
  | succ fuel ih =>
    simp only [cycleRunAux]
    -- After one cycleStep, either halted or stepsSimulated increased
    have hprog := cycleStep_progress table fallback thresh dmaxes st
    set st' := cycleStep table fallback thresh dmaxes st with hst'_def
    -- Apply IH to the recursive call
    have hih := ih st'
    rcases hprog with hhalted | hge
    · -- cycleStep halted: the recursive call preserves halted
      have hst'_halted := hhalted
      -- cycleRunAux on a halted state returns a halted state
      left
      rcases hih with h | h
      · exact h
      · -- st' is halted, so cycleRunAux preserves that
        exact cycleRunAux_halted_stable _ _ _ _ _ _ hst'_halted
    · -- cycleStep not halted: stepsSimulated grew by ≥ 1
      rcases hih with h | h
      · left; exact h
      · right; omega

/-- One step of `cycleStep` preserves the naiveRun invariant and buffer invariant.
    If `naiveRun prog n stepsSimulated = some (unfmap m)` before the step,
    the same holds after (with updated stepsSimulated and m).
    If the step halts, additionally `naiveStep` returns `none`. -/
theorem cycleStep_correct
    (prog : FractranProg) (n : ℕ)
    (hw : prog.WellFormed) (hn : 0 < n)
    (table : Array (List Candidate)) (fallback : List Candidate)
    (thresh dmaxes : RegMap) (st : CycleState)
    (htable : table = optTable prog.toRegProg)
    (hfallback : fallback = allCandidates prog.toRegProg)
    (hthresh : thresh = dthreshMap prog.toRegProg st.buf.cap)
    (hdmaxes : dmaxes = dmaxesMap prog.toRegProg)
    (hinv : naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m))
    (hhalted_inv : st.halted → naiveStep prog (RegMap.unfmap st.m) = none)
    (hwf : RegMap.WF st.m)
    (helim : ElimInvariant prog.toRegProg st.cands st.m)
    (hbuf : BufferInvariant prog n thresh st.buf st.stepsSimulated) :
    let st' := cycleStep table fallback thresh dmaxes st
    (naiveRun prog n st'.stepsSimulated = some (RegMap.unfmap st'.m)) ∧
    (st'.halted → naiveStep prog (RegMap.unfmap st'.m) = none) ∧
    RegMap.WF st'.m ∧
    ElimInvariant prog.toRegProg st'.cands st'.m ∧
    BufferInvariant prog n thresh st'.buf st'.stepsSimulated := by
  unfold cycleStep
  cases hh : st.halted
  · -- Not halted
    -- Eliminate the `if st.halted` (which became `if false = true`)
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Helper: bridge elimStep to naiveStep
    have helim_bridge : ∀ (i : ℕ) (m' : RegMap),
        elimStep st.cands st.m = some (i, m') →
        naiveStep prog (RegMap.unfmap st.m) = some (RegMap.unfmap m') ∧
        RegMap.WF m' := by
      intro i m' hes
      have hrs : regStep prog.toRegProg st.m = some m' := by
        have := elimStep_eq_regStep prog.toRegProg st.cands st.m helim
        simp [hes] at this; exact this.symm
      constructor
      · have := regStep_correct prog st.m hwf hw
        simp [hrs] at this; exact this.symm
      · exact regStep_wf prog st.m hwf hw m' hrs
    have hhalt_bridge : elimStep st.cands st.m = none →
        naiveStep prog (RegMap.unfmap st.m) = none := by
      intro hes
      have hrs : regStep prog.toRegProg st.m = none := by
        have := elimStep_eq_regStep prog.toRegProg st.cands st.m helim
        simp [hes] at this; exact this.symm
      have := regStep_correct prog st.m hwf hw
      simp [hrs] at this; exact this.symm
    -- Helper for halt case
    have halt_case : elimStep st.cands st.m = none →
        (naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m)) ∧
        (true = true → naiveStep prog (RegMap.unfmap st.m) = none) ∧
        RegMap.WF st.m ∧
        ElimInvariant prog.toRegProg st.cands st.m ∧
        BufferInvariant prog n thresh st.buf st.stepsSimulated :=
      fun hes => ⟨hinv, fun _ => hhalt_bridge hes, hwf, helim, hbuf⟩
    -- Helper: produce the 5-tuple for the normal step case with insert
    have normal_step_insert : ∀ (i : ℕ) (m' : RegMap),
        elimStep st.cands st.m = some (i, m') →
        let nextCands := if h : i < table.size then table[i] else fallback
        let st' : CycleState := { m := m', cands := nextCands,
                                   buf := st.buf.insert (stateSplit thresh st.m),
                                   stepsSimulated := st.stepsSimulated + 1 }
        (naiveRun prog n st'.stepsSimulated = some st'.m.unfmap) ∧
        (st'.halted → naiveStep prog st'.m.unfmap = none) ∧
        st'.m.WF ∧ ElimInvariant prog.toRegProg st'.cands st'.m ∧
        BufferInvariant prog n thresh st'.buf st'.stepsSimulated := by
      intro i m' hes
      have ⟨hstep, hwf'⟩ := helim_bridge i m' hes
      refine ⟨?_, by intro h; simp at h, hwf', ?_, ?_⟩
      · -- naiveRun
        change naiveRun prog n st.stepsSimulated >>= naiveStep prog = some (RegMap.unfmap m')
        rw [hinv]; exact hstep
      · -- ElimInvariant
        subst htable; subst hfallback
        by_cases hi : i < (optTable prog.toRegProg).size
        · simp only [dif_pos hi]
          exact optTable_preserves_invariant prog.toRegProg st.cands st.m helim i m' hes hi
        · simp only [dif_neg hi]
          exact allCandidates_invariant prog.toRegProg m'
      · -- BufferInvariant (insert case)
        exact bufferInvariant_insert prog n thresh st.buf st.stepsSimulated st.m
          hbuf hinv hwf
    -- Helper: produce the 5-tuple for normal step with empty buffer
    have normal_step_empty : ∀ (i : ℕ) (m' : RegMap),
        elimStep st.cands st.m = some (i, m') →
        let nextCands := if h : i < table.size then table[i] else fallback
        let st' : CycleState := { m := m', cands := nextCands,
                                   buf := CBuf.empty st.buf.cap st.buf.hCapPos,
                                   stepsSimulated := st.stepsSimulated + 1 }
        (naiveRun prog n st'.stepsSimulated = some st'.m.unfmap) ∧
        (st'.halted → naiveStep prog st'.m.unfmap = none) ∧
        st'.m.WF ∧ ElimInvariant prog.toRegProg st'.cands st'.m ∧
        BufferInvariant prog n thresh st'.buf st'.stepsSimulated := by
      intro i m' hes
      have ⟨hstep, hwf'⟩ := helim_bridge i m' hes
      refine ⟨?_, by intro h; simp at h, hwf', ?_, ?_⟩
      · change naiveRun prog n st.stepsSimulated >>= naiveStep prog = some (RegMap.unfmap m')
        rw [hinv]; exact hstep
      · subst htable; subst hfallback
        by_cases hi : i < (optTable prog.toRegProg).size
        · simp only [dif_pos hi]
          exact optTable_preserves_invariant prog.toRegProg st.cands st.m helim i m' hes hi
        · simp only [dif_neg hi]
          exact allCandidates_invariant prog.toRegProg m'
      · exact bufferInvariant_empty prog n thresh st.buf.cap st.buf.hCapPos _
    -- Case split via tactic-mode match
    match hgr : st.buf.getRange Prod.snd (stateSplit thresh st.m).snd with
    | none =>
      dsimp only
      match hes : elimStep st.cands st.m with
      | none => exact halt_case hes
      | some (i, m') => exact normal_step_insert i m' hes
    | some range =>
      dsimp only
      match hlc : leapCount dmaxes
          ((stateSplit thresh st.m).fst :: (range.dropLast.map Prod.fst))
          ((range.getLast!).fst) ((stateSplit thresh st.m).fst) with
      | none =>
        dsimp only
        match hes : elimStep st.cands st.m with
        | none => exact halt_case hes
        | some (i, m') => exact normal_step_empty i m' hes
      | some c =>
        dsimp only
        by_cases hc : c = 0
        · simp only [hc, ↓reduceIte]
          match hes : elimStep st.cands st.m with
          | none => exact halt_case hes
          | some (i, m') => exact normal_step_empty i m' hes
        · -- Leap case: c > 0
          simp only [show c ≠ 0 from hc, ↓reduceIte]
          have hcpos : 0 < c := Nat.pos_of_ne_zero hc
          have hrange_ne : range ≠ [] := by
            have := CBuf.getRange_length_pos st.buf Prod.snd (stateSplit thresh st.m).snd range hgr
            exact List.ne_nil_of_length_pos this
          have hstartData_wf : (range.getLast!).fst.WF := by
            have hlen := CBuf.getRange_length_pos st.buf Prod.snd
              (stateSplit thresh st.m).snd range hgr
            have hne : range ≠ [] := List.ne_nil_of_length_pos hlen
            -- getLast! = getLast for nonempty lists
            rw [show range.getLast! = range.getLast hne from by
              exact List.getLast!_of_getLast? (List.getLast?_eq_some_getLast hne)]
            -- range is a prefix of buf.toList
            have hsub : ∀ x ∈ range, x ∈ st.buf.toList := by
              have hgr' := hgr
              simp only [CBuf.getRange, Option.map_eq_some_iff] at hgr'
              obtain ⟨idx, _, rfl⟩ := hgr'
              exact fun x hx => List.take_subset _ _ hx
            exact bufferInvariant_fst_wf prog n thresh st.buf st.stepsSimulated hbuf
              _ (hsub _ (List.getLast_mem hne))
          refine ⟨?_, by intro h; simp at h,
                  leapState_wf _ _ _ _
                    hstartData_wf
                    (stateSplit_wf_fst thresh st.m hwf)
                    (stateSplit_wf_snd thresh st.m hwf),
                  hfallback ▸ allCandidates_invariant prog.toRegProg _, ?_⟩
          · -- naiveRun correctness of the leap
            exact leap_correct prog n hw hn thresh dmaxes st
              hthresh hdmaxes hinv hwf hbuf range hgr c hcpos hlc
          · -- Buffer invariant (buffer is emptied after leap)
            exact bufferInvariant_empty prog n thresh st.buf.cap st.buf.hCapPos _
  · -- Already halted: cycleStep returns st unchanged
    simp only [↓reduceIte]
    exact ⟨hinv, hhalted_inv, hwf, helim, hbuf⟩

/-- **Interpreter invariant.**
    If `cycleRunAux` starts from a state matching `naiveRun`, it maintains
    that correspondence:
    - `naiveRun prog n result.stepsSimulated = some (unfmap result.m)` (if not halted)
    - `naiveStep prog (unfmap result.m) = none` (if halted)

    The proof has two cases:
    - **Normal steps** (no leap): each `elimStep` corresponds to one `naiveStep`,
      which is already proven in `elimRun_correct`.
    - **Leap steps**: `leapState` agrees with running `naiveRun` for
      `range.length * c` additional steps. This requires `cycle_properties`
      (proven above) plus bridge lemmas connecting `leapState` to iterated
      `naiveStep`. The mathematical core is fully proven; the remaining gap
      is bridging `leapState` to `naiveRun` via `regRun_eq` and `facmap_unfmap`. -/
theorem cycleRunAux_correct
    (prog : FractranProg) (n : ℕ)
    (hw : prog.WellFormed) (hn : 0 < n)
    (table : Array (List Candidate)) (fallback : List Candidate)
    (thresh dmaxes : RegMap) (st : CycleState) (fuel : ℕ)
    (htable : table = optTable prog.toRegProg)
    (hfallback : fallback = allCandidates prog.toRegProg)
    (hthresh : thresh = dthreshMap prog.toRegProg st.buf.cap)
    (hdmaxes : dmaxes = dmaxesMap prog.toRegProg)
    (hinit : naiveRun prog n st.stepsSimulated = some (RegMap.unfmap st.m))
    (hhalted : st.halted → naiveStep prog (RegMap.unfmap st.m) = none)
    (hwf : RegMap.WF st.m)
    (helim : ElimInvariant prog.toRegProg st.cands st.m)
    (hbuf : BufferInvariant prog n thresh st.buf st.stepsSimulated) :
    let result := cycleRunAux table fallback thresh dmaxes st fuel
    if result.halted then
      naiveRun prog n result.stepsSimulated = some (RegMap.unfmap result.m) ∧
      naiveStep prog (RegMap.unfmap result.m) = none
    else
      naiveRun prog n result.stepsSimulated = some (RegMap.unfmap result.m) := by
  induction fuel generalizing st with
  | zero =>
    simp only [cycleRunAux]
    cases hh : st.halted
    · exact hinit
    · exact ⟨hinit, hhalted hh⟩
  | succ fuel ih =>
    simp only [cycleRunAux]
    have hstep := cycleStep_correct prog n hw hn table fallback thresh dmaxes st
      htable hfallback hthresh hdmaxes hinit hhalted hwf helim hbuf
    obtain ⟨hinv', hhalted', hwf', helim', hbuf'⟩ := hstep
    have hthresh' : thresh = dthreshMap prog.toRegProg
        (cycleStep table fallback thresh dmaxes st).buf.cap := by
      rw [hthresh, cycleStep_preserves_cap]
    exact ih _ hthresh' hinv' hhalted' hwf' helim' hbuf'

/-- **The cycle-detecting interpreter is correct.**
    For any cycle buffer capacity, the interpreter satisfies `Correct`:
    it returns `(result, j)` with `j ≥ k` and `naiveRun prog n j = result`.

    Proof structure:
    - **Fuel bound** (`cycleRunAux_stepsSimulated_ge`): if not halted,
      `stepsSimulated ≥ k`, so `j ≥ k`. If halted, `j = max ... k ≥ k`.
    - **Correctness** (`cycleRunAux_correct`): the state matches `naiveRun`
      at the reported step count. For halts, `naiveRun` at `stepsSimulated + 1`
      is `none`, extended to `j` by `naiveRun_none_of_ge`. -/
theorem cycleRun_correct (cyclen : ℕ) (hcyclen : 0 < cyclen) :
    Correct (cycleRunNat cyclen hcyclen) := by
  intro prog n k hw hn
  -- The key intermediate computation
  let table := optTable prog.toRegProg
  let cands := allCandidates prog.toRegProg
  let thresh := dthreshMap prog.toRegProg cyclen
  let dmaxes := dmaxesMap prog.toRegProg
  let initState : CycleState :=
    { m := RegMap.facmap n, cands := cands, buf := CBuf.empty cyclen hcyclen,
      stepsSimulated := 0 }
  let result := cycleRunAux table cands thresh dmaxes initState k
  -- Show that cycleRunNat equals a specific value depending on halted
  -- (this is just the definition of cycleRunNat)
  have hdef : cycleRunNat cyclen hcyclen prog n k =
      if result.halted then (none, result.stepsSimulated)
      else (some result.m.unfmap, result.stepsSimulated) := rfl
  -- Initial invariant
  have hinit : naiveRun prog n 0 = some (RegMap.unfmap (RegMap.facmap n)) := by
    simp [naiveRun, RegMap.facmap_unfmap n hn]
  have hinit' : naiveRun prog n initState.stepsSimulated = some initState.m.unfmap := hinit
  -- Core lemmas with explicit types (avoiding let-in-type issues)
  have hcorr : if result.halted then
        naiveRun prog n result.stepsSimulated = some result.m.unfmap ∧
        naiveStep prog result.m.unfmap = none
      else naiveRun prog n result.stepsSimulated = some result.m.unfmap :=
    cycleRunAux_correct prog n hw hn table cands thresh dmaxes initState k
      rfl rfl (by simp [initState, thresh]) rfl hinit'
      (by simp [initState]) (RegMap.facmap_wf n) (allCandidates_invariant prog.toRegProg _)
      (bufferInvariant_empty prog n thresh cyclen hcyclen 0)
  have hge : result.halted ∨ result.stepsSimulated ≥ initState.stepsSimulated + k :=
    cycleRunAux_stepsSimulated_ge table cands thresh dmaxes initState k
  -- Case split on halted
  cases hh : result.halted
  · -- Not halted (result.halted = false)
    simp only [hh, Bool.false_eq_true, ↓reduceIte] at hcorr
    simp only [hh, Bool.false_eq_true, false_or] at hge
    rw [hdef]
    simp only [hh, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, hcorr⟩
  · -- Halted (result.halted = true): produce HaltsIn at result.stepsSimulated
    simp only [hh, ↓reduceIte] at hcorr
    obtain ⟨hrun, hstep⟩ := hcorr
    rw [hdef]; simp only [hh, ite_true]
    exact ⟨result.m.unfmap, hrun, hstep⟩
