import Fractran.Register

/-!
# Static Fraction Elimination

After fraction `j` fires, some fractions `k < j` provably cannot fire next.
Specifically, if `den_k` shares no prime with `num_j`, then `k`'s denominator
requirements can only have worsened (the primes it needs either stayed the same
or decreased), so `k` remains inapplicable.

`optTable` precomputes, for each fraction index, the narrowed candidate list
for the next step. `elimStep` scans only the candidates, returning both the
fraction index (needed to look up the next candidate list) and the new state.

This module is used both standalone (via `elimRunNat`, proven `Correct`) and
as a building block for the cycle-detecting interpreter, which threads the
candidate list through its own control loop and resets to the full list after
arithmetic leaps.

## Candidate list format

A candidate list has type `List ((RegMap × RegMap) × Nat)` — each entry is a
fraction `(num, den)` paired with its index in the original program. This
matches the output of `List.zipIdx` on the register program.
-/

/-! ## Definitions -/

/-- Two register maps share at least one key (prime factor). -/
def RegMap.sharesKey (a b : RegMap) : Bool :=
  a.toList.any fun (p, _) => b.contains p

/-- A candidate entry: a fraction `(num, den)` paired with its program index. -/
abbrev Candidate := (RegMap × RegMap) × Nat

/-- Full indexed fraction list: each fraction paired with its program index.
    Used as the initial candidate list and after cycle-detection leaps. -/
def allCandidates (prog : List (RegMap × RegMap)) : List Candidate :=
  prog.zipIdx

/-- Precompute the candidate table. Entry `i` lists the fractions that could
    fire after fraction `i` fires:
    - All fractions `j ≥ i` (always candidates — their position means they
      weren't checked before `i`)
    - Fractions `k < i` only if `den_k` shares a prime with `num_i`
      (otherwise `k` was already inapplicable and can only have gotten worse) -/
def optTable (prog : List (RegMap × RegMap)) : Array (List Candidate) :=
  let indexed := allCandidates prog
  Array.ofFn fun (i : Fin prog.length) =>
    let (pre, post) := List.splitAt i.val indexed
    let num := prog[i].1
    List.filter (fun ((_, den), _) => RegMap.sharesKey num den) pre ++ post

@[simp] theorem optTable_size (prog : List (RegMap × RegMap)) :
    (optTable prog).size = prog.length := by
  simp [optTable]

/-- One step with a candidate list: find the first applicable fraction.
    Returns the fraction's program index and the resulting register state,
    or `none` if no candidate applies (the program halts).

    This is the per-step primitive shared by both the standalone elimination
    interpreter and the cycle-detecting interpreter. -/
def elimStep (candidates : List Candidate) (m : RegMap) :
    Option (Nat × RegMap) :=
  candidates.findSome? fun ((num, den), i) =>
    if RegMap.applicable den m then some (i, RegMap.applyFrac num den m) else none

/-! ## Standalone elimination interpreter -/

/-- Run the elimination interpreter for `k` steps, threading the candidate
    list: after fraction `i` fires, the next step scans `table[i]`.
    Returns `(state, candidates)` or `none` if halted. -/
def elimRunAux (table : Array (List Candidate))
    (fallback : List Candidate)
    (m : RegMap) (cands : List Candidate) :
    Nat → Option (RegMap × List Candidate)
  | 0 => some (m, cands)
  | k + 1 => do
    let (m', cands') ← elimRunAux table fallback m cands k
    let (i, m'') ← elimStep cands' m'
    let nextCands := if h : i < table.size then table[i] else fallback
    return (m'', nextCands)

/-- Run the elimination interpreter, returning only the final state. -/
def elimRun (table : Array (List Candidate))
    (fallback : List Candidate)
    (m : RegMap) (cands : List Candidate) (k : Nat) : Option RegMap :=
  (elimRunAux table fallback m cands k).map Prod.fst

/-- Halt-aware variant of `elimRunAux`: returns the result and the exact number
    of successful steps. If the program halts before fuel runs out, the step
    count is the count of successful steps before halting; otherwise it is `k`. -/
def elimRunExactAux (table : Array (List Candidate)) (fallback : List Candidate) :
    RegMap → List Candidate → Nat → Option (RegMap × List Candidate) × Nat
  | m, cands, 0     => (some (m, cands), 0)
  | m, cands, k + 1 =>
    match elimStep cands m with
    | none         => (none, 0)
    | some (i, m') =>
      let nextCands := if h : i < table.size then table[i] else fallback
      let res := elimRunExactAux table fallback m' nextCands k
      (res.1, res.2 + 1)

/-- Nat-level elimination interpreter conforming to the `Correct` interface.
    When still running after `k` steps, returns `(some m, k)`. When halted,
    returns `(none, j)` where `j` is the exact number of successful steps. -/
def elimRunNat (prog : FractranProg) (n k : ℕ) : Option ℕ × ℕ :=
  let regProg := prog.toRegProg
  let table := optTable regProg
  let cands := allCandidates regProg
  let (r, j) := elimRunExactAux table cands (RegMap.facmap n) cands k
  (r.map (fun mc => RegMap.unfmap mc.1), j)

/-! ## Invariant -/

/-- The elimination invariant: `candidates` is a sublist of the full indexed
    program (preserving scan order), and every omitted fraction is inapplicable
    on the current state `m`. Under this invariant, `elimStep` finds the same
    first applicable fraction as `regStep`. -/
def ElimInvariant (prog : List (RegMap × RegMap))
    (candidates : List Candidate) (m : RegMap) : Prop :=
  List.Sublist candidates (allCandidates prog) ∧
    ∀ entry ∈ allCandidates prog, entry ∉ candidates →
      ¬ RegMap.applicable entry.1.2 m

/-- The full candidate list trivially satisfies the invariant. -/
theorem allCandidates_invariant (prog : List (RegMap × RegMap)) (m : RegMap) :
    ElimInvariant prog (allCandidates prog) m :=
  ⟨List.Sublist.refl _, fun _ h hn => absurd h hn⟩

/-! ## Helper lemmas -/

section Helpers

open List

/-- `allCandidates` produces a `Nodup` list (indices are unique). -/
theorem nodup_allCandidates (prog : List (RegMap × RegMap)) :
    (allCandidates prog).Nodup := by
  unfold allCandidates
  suffices h : ∀ n, (prog.zipIdx n).Nodup from h 0
  intro n
  induction prog generalizing n with
  | nil => exact nodup_nil
  | cons a rest ih =>
    rw [zipIdx_cons, nodup_cons]
    exact ⟨fun hmem => absurd (le_snd_of_mem_zipIdx hmem) (by omega),
           ih (n + 1)⟩

/-- `findSome?` on a sublist agrees with the full list when the full list
    has no duplicates and every removed element maps to `none`. -/
private theorem findSome?_sublist {l₁ l₂ : List α} {f : α → Option β}
    (hsub : l₁ <+ l₂)
    (hnd : l₂.Nodup)
    (hnone : ∀ x ∈ l₂, x ∉ l₁ → f x = none) :
    l₁.findSome? f = l₂.findSome? f := by
  induction hsub with
  | slnil => rfl
  | cons a hsub' ih =>
    rw [nodup_cons] at hnd
    have ha_none : f a = none :=
      hnone a (mem_cons_self ..) (fun h => hnd.1 (hsub'.subset h))
    rw [findSome?_cons_of_isNone (by simp [ha_none])]
    exact ih hnd.2 (fun x hx hnx => hnone x (mem_cons.mpr (Or.inr hx)) hnx)
  | cons_cons a hsub' ih =>
    rw [nodup_cons] at hnd
    simp only [findSome?_cons]
    cases f a
    · exact ih hnd.2 fun x hx hnx =>
        hnone x (mem_cons.mpr (Or.inr hx)) fun hmem => by
          rcases mem_cons.mp hmem with rfl | h
          · exact absurd hx hnd.1
          · exact absurd h hnx
    · rfl

/-- Dropping the index from `elimStep` on a `zipIdx`-ed list recovers `regStep`.
    Generalized over the starting index. -/
private theorem findSome?_zipIdx_snd (prog : List (RegMap × RegMap)) (m : RegMap) (n : Nat) :
    (prog.zipIdx n |>.findSome? fun ((num, den), i) =>
      if RegMap.applicable den m then some (i, RegMap.applyFrac num den m) else none
    ).map Prod.snd =
    prog.findSome? fun (num, den) =>
      if RegMap.applicable den m then some (RegMap.applyFrac num den m) else none := by
  induction prog generalizing n with
  | nil => simp
  | cons frac rest ih =>
    obtain ⟨num, den⟩ := frac
    simp only [zipIdx_cons, findSome?_cons]
    cases RegMap.applicable den m
    · dsimp; exact ih (n + 1)
    · dsimp

/-- If `¬sharesKey num den_e`, then for any `p` that is a key of `den_e`,
    `p` is not a key of `num`. -/
private theorem not_mem_of_sharesKey_false {num den_e : RegMap} {p : ℕ}
    (hnokey : RegMap.sharesKey num den_e = false) (hp : p ∈ den_e) : p ∉ num := by
  intro hp_num
  simp only [RegMap.sharesKey] at hnokey
  rw [List.any_eq_false] at hnokey
  have hmem : (p, num.getD p 0) ∈ num.toList :=
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr
      (Std.TreeMap.getElem?_eq_some_getD_of_contains
        (Std.TreeMap.contains_iff_mem.mpr hp_num))
  have := hnokey _ hmem
  simp [Std.TreeMap.contains_iff_mem.mpr hp] at this

/-- If `¬sharesKey num den_e` and `¬applicable den_e m`, then
    `¬applicable den_e (applyFrac num den m)`. Primes in `den_e` are disjoint
    from `num`, so applying fraction `(num, den)` can only decrease those exponents. -/
theorem inapplicable_preserved (num den den_e m : RegMap)
    (hnokey : RegMap.sharesKey num den_e = false)
    (hinapp : RegMap.applicable den_e m = false) :
    RegMap.applicable den_e (RegMap.applyFrac num den m) = false := by
  -- Contrapositive: applicable on m' ⟹ applicable on m
  rw [Bool.eq_false_iff] at hinapp ⊢
  intro happ_m'; apply hinapp
  rw [RegMap.applicable_eq_toList_all] at happ_m' ⊢
  rw [List.all_eq_true] at happ_m' ⊢
  intro ⟨p, e⟩ hmem
  have h := happ_m' ⟨p, e⟩ hmem
  simp only [decide_eq_true_eq] at h ⊢
  -- h : (applyFrac num den m).getD p 0 ≥ e
  -- Suffices: m'.getD p 0 ≤ m.getD p 0 (for p ∈ den_e, p ∉ num)
  have hp_in_den_e : p ∈ den_e :=
    Std.TreeMap.mem_iff_isSome_getElem?.mpr (by
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hmem]; rfl)
  have hp_notin_num : p ∉ num := not_mem_of_sharesKey_false hnokey hp_in_den_e
  have hle : (RegMap.applyFrac num den m).getD p 0 ≤ m.getD p 0 := by
    simp only [RegMap.applyFrac]
    rw [RegMap.mul_getD, RegMap.div_getD, Std.TreeMap.getD_eq_fallback hp_notin_num]
    omega
  omega

end Helpers

/-! ## Correctness -/

section Correctness

open List

/-- `elimStep` on the full candidate list agrees with `regStep`
    (ignoring the index). -/
theorem elimStep_allCandidates (prog : List (RegMap × RegMap)) (m : RegMap) :
    (elimStep (allCandidates prog) m).map Prod.snd = regStep prog m := by
  exact findSome?_zipIdx_snd prog m 0

/-- Under the elimination invariant, `elimStep` agrees with `regStep`. -/
theorem elimStep_eq_regStep (prog : List (RegMap × RegMap))
    (candidates : List Candidate) (m : RegMap)
    (hinv : ElimInvariant prog candidates m) :
    (elimStep candidates m).map Prod.snd = regStep prog m := by
  rw [← elimStep_allCandidates]
  simp only [elimStep]
  congr 1
  exact findSome?_sublist hinv.1 (nodup_allCandidates prog)
    (fun entry hmem hnotin => by
      have hinapp := hinv.2 entry hmem hnotin
      simp only [Bool.not_eq_true] at hinapp
      simp [hinapp])

/-- After fraction `i` fires as the first applicable fraction on state `m`,
    `optTable[i]` satisfies the invariant on the resulting state. -/
theorem optTable_preserves_invariant (prog : List (RegMap × RegMap))
    (candidates : List Candidate) (m : RegMap)
    (hinv : ElimInvariant prog candidates m)
    (i : Nat) (m' : RegMap)
    (hstep : elimStep candidates m = some (i, m'))
    (hi : i < (optTable prog).size) :
    ElimInvariant prog ((optTable prog)[i]'hi) m' := by
  rw [optTable_size] at hi
  -- Step 1: Lift elimStep from candidates to allCandidates via findSome?_sublist
  have hstep_all : elimStep (allCandidates prog) m = some (i, m') := by
    simp only [elimStep] at hstep ⊢
    rwa [← findSome?_sublist hinv.1 (nodup_allCandidates prog)
      (fun entry hmem hnotin => by
        have := hinv.2 entry hmem hnotin
        simp [Bool.not_eq_true] at this; simp [this])]
  -- Step 2: Decompose findSome? on allCandidates
  simp only [elimStep, allCandidates] at hstep_all
  rw [findSome?_eq_some_iff] at hstep_all
  obtain ⟨pre, ⟨⟨num_i, den_i⟩, idx⟩, post, hdecomp, hfire, hpre_none⟩ := hstep_all
  -- Parse the if-then-else: applicable → idx = i ∧ m' = applyFrac
  have happ_i : RegMap.applicable den_i m = true := by
    by_contra h; simp [Bool.not_eq_true] at h; simp [h] at hfire
  simp only [happ_i, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hfire
  have hidx : idx = i := hfire.1
  have hm' : m' = RegMap.applyFrac num_i den_i m := hfire.2.symm
  rw [hidx] at hdecomp
  -- Step 3: pre.length = i (the matched entry is at position i)
  have hlen_pre : pre.length = i := by
    have h1 : (prog.zipIdx)[pre.length]? = some ((num_i, den_i), i) := by
      rw [hdecomp]; simp
    rw [getElem?_zipIdx] at h1
    have hlt : pre.length < prog.length := by
      have := congrArg List.length hdecomp; simp [length_zipIdx] at this; omega
    simp [hlt] at h1; omega
  -- Step 4: All entries in pre (= take i allCandidates) are inapplicable on m
  have hpre_eq : pre = (allCandidates prog).take i := by
    have : (allCandidates prog).take i = (pre ++ ((num_i, den_i), i) :: post).take pre.length := by
      rw [← hdecomp, ← hlen_pre]; rfl
    rw [this, List.take_left]
  have hall_pre_inapp : ∀ entry ∈ (allCandidates prog).take i,
      ¬ RegMap.applicable entry.1.2 m := by
    intro entry hmem; rw [← hpre_eq] at hmem
    have := hpre_none entry hmem
    intro hcontra; simp [hcontra] at this
  -- Step 5: (num_i, den_i) = prog[i]
  have hprog_get : (num_i, den_i) = prog[i] := by
    have h1 : (prog.zipIdx)[i]? = some ((num_i, den_i), i) := by
      rw [hdecomp, ← hlen_pre]; simp
    rw [getElem?_zipIdx] at h1
    simp [hi] at h1; exact h1.symm
  -- Step 6: Characterize optTable[i] membership
  have hi_ot : i < (optTable prog).size := by rw [optTable_size]; exact hi
  -- Key lemma: entry ∈ optTable[i] ↔ entry ∈ filter f (take i ac) ∨ entry ∈ drop i ac
  have hmem_opt : ∀ entry, entry ∈ (optTable prog)[i]'hi_ot ↔
      (entry ∈ (allCandidates prog).drop i ∨
       (entry ∈ (allCandidates prog).take i ∧
        RegMap.sharesKey num_i entry.1.2 = true)) := by
    intro entry
    simp only [optTable, Array.getElem_ofFn, splitAt_eq]
    constructor
    · intro h
      rw [mem_append] at h
      rcases h with h | h
      · right
        rw [mem_filter] at h
        refine ⟨h.1, ?_⟩
        -- sharesKey equivalence: prog[⟨i,⋯⟩].1 = num_i
        convert h.2 using 2
        exact hprog_get.symm ▸ rfl
      · exact Or.inl h
    · intro h
      rw [mem_append]
      rcases h with h | ⟨hmem, hshare⟩
      · exact Or.inr h
      · left; rw [mem_filter]
        refine ⟨hmem, ?_⟩
        convert hshare using 2
        exact hprog_get.symm ▸ rfl
  refine ⟨?_, ?_⟩
  · -- Sublist: optTable[i] <+ allCandidates prog
    -- optTable[i] = filter f (take i ac) ++ drop i ac
    -- filter f (take i ac) <+ take i ac, and drop i ac <+ drop i ac
    -- so filter f (take i ac) ++ drop i ac <+ take i ac ++ drop i ac = ac
    have hsub : (optTable prog)[i]'hi_ot <+ allCandidates prog := by
      simp only [optTable, Array.getElem_ofFn, splitAt_eq]
      conv_rhs => rw [← take_append_drop i (allCandidates prog)]
      exact Sublist.append (filter_sublist.trans (Sublist.refl _)) (Sublist.refl _)
    exact hsub
  · -- Inapplicability of excluded entries
    intro entry hmem_all hnotin
    rw [hmem_opt] at hnotin
    simp only [not_or, not_and] at hnotin
    -- entry is not in drop i, so it's in take i
    have hmem_take : entry ∈ (allCandidates prog).take i := by
      have := (mem_append.mp (take_append_drop i (allCandidates prog) ▸ hmem_all))
      exact this.elim id (fun h => absurd h hnotin.1)
    -- sharesKey is false for this entry
    have hnokey : RegMap.sharesKey num_i entry.1.2 = false := by
      cases h : RegMap.sharesKey num_i entry.1.2
      · rfl
      · exact absurd h (hnotin.2 hmem_take)
    -- entry was inapplicable on m, remains inapplicable on m'
    have hinapp : RegMap.applicable entry.1.2 m = false := by
      simpa [Bool.not_eq_true] using hall_pre_inapp entry hmem_take
    rw [hm', Bool.not_eq_true]
    exact inapplicable_preserved num_i den_i entry.1.2 m hnokey hinapp

/-- `elimRunAux` agrees with `regRun` on the state component, and preserves
    the elimination invariant at every intermediate step. -/
theorem elimRunAux_spec (regProg : List (RegMap × RegMap))
    (k : Nat) (m : RegMap) (cands : List Candidate)
    (hinv : ElimInvariant regProg cands m) :
    (elimRunAux (optTable regProg) (allCandidates regProg) m cands k).map Prod.fst =
      regRun regProg m k ∧
    (∀ m' cands',
      elimRunAux (optTable regProg) (allCandidates regProg) m cands k = some (m', cands') →
      ElimInvariant regProg cands' m') := by
  induction k generalizing m cands with
  | zero =>
    constructor
    · simp [elimRunAux, regRun]
    · intro _ _ h
      simp only [elimRunAux, Option.some.injEq, Prod.mk.injEq] at h
      exact h.1 ▸ h.2 ▸ hinv
  | succ k ih =>
    have ⟨ih_eq, ih_inv⟩ := ih m cands hinv
    cases hk : elimRunAux (optTable regProg) (allCandidates regProg) m cands k with
    | none =>
      simp only [hk, Option.map_none] at ih_eq
      constructor
      · simp [elimRunAux, regRun, hk, ← ih_eq]
      · intro _ _ h; simp [elimRunAux, hk] at h
    | some p =>
      obtain ⟨m', cands'⟩ := p
      simp only [hk, Option.map_some] at ih_eq
      have hinv' := ih_inv m' cands' hk
      have hstep_eq := elimStep_eq_regStep regProg cands' m' hinv'
      cases hs : elimStep cands' m' with
      | none =>
        simp only [hs, Option.map_none] at hstep_eq
        constructor
        · simp [elimRunAux, regRun, hk, hs, ← ih_eq, ← hstep_eq]
        · intro _ _ h; simp [elimRunAux, hk, hs] at h
      | some q =>
        obtain ⟨i, m''⟩ := q
        simp only [hs, Option.map_some] at hstep_eq
        constructor
        · simp [elimRunAux, regRun, hk, hs, ← ih_eq, ← hstep_eq]
        · intro m₂ cands₂ heq
          obtain ⟨rfl, heq2⟩ :=
            by simpa [elimRunAux, hk, hs] using heq
          split at heq2
          · next hi =>
            rw [← heq2]
            exact optTable_preserves_invariant regProg cands' m'
              hinv' i m'' hs (optTable_size regProg ▸ hi)
          · rw [← heq2]
            exact allCandidates_invariant regProg m''

/-- Specification of `elimRunExactAux`. Either it ran the full `k` steps without
    halting (and the state matches `regRun`), or it halted at some step `j ≤ k`. -/
lemma elimRunExactAux_correct (regProg : List (RegMap × RegMap))
    (k : Nat) (m : RegMap) (cands : List Candidate)
    (hinv : ElimInvariant regProg cands m) :
    let (r, j) := elimRunExactAux (optTable regProg) (allCandidates regProg) m cands k
    (∀ m' c', r = some (m', c') → j = k ∧ regRun regProg m k = some m') ∧
    (r = none → j ≤ k ∧ ∃ m_halt, regRun regProg m j = some m_halt ∧
      regStep regProg m_halt = none) := by
  induction k generalizing m cands with
  | zero =>
    simp only [elimRunExactAux]
    refine ⟨?_, ?_⟩
    · intro m' c' h
      have : (m, cands) = (m', c') := Option.some.inj h
      have hm_eq : m' = m := (Prod.mk.inj this).1.symm
      refine ⟨trivial, ?_⟩
      rw [hm_eq]; rfl
    · intro h; exact absurd h (by simp)
  | succ k ih =>
    simp only [elimRunExactAux]
    have hstep_eq := elimStep_eq_regStep regProg cands m hinv
    cases hs : elimStep cands m with
    | none =>
      simp only [hs, Option.map_none] at hstep_eq
      refine ⟨?_, ?_⟩
      · intro m' c' h; exact absurd h (by simp)
      · intro _
        refine ⟨Nat.zero_le _, m, rfl, hstep_eq.symm⟩
    | some im' =>
      obtain ⟨i, m'⟩ := im'
      simp only [hs, Option.map_some] at hstep_eq
      have hregstep : regStep regProg m = some m' := hstep_eq.symm
      have hinv' : ElimInvariant regProg
          (if h : i < (optTable regProg).size then (optTable regProg)[i] else allCandidates regProg)
          m' := by
        split
        · next hi => exact optTable_preserves_invariant regProg cands m hinv i m' hs hi
        · exact allCandidates_invariant regProg m'
      have ih_m' := ih m' _ hinv'
      cases hres : elimRunExactAux (optTable regProg) (allCandidates regProg) m'
          (if h : i < (optTable regProg).size then (optTable regProg)[i]
           else allCandidates regProg) k with
      | mk r j =>
        simp only [hres] at ih_m' ⊢
        obtain ⟨ih1, ih2⟩ := ih_m'
        refine ⟨?_, ?_⟩
        · intro m'' c'' h
          obtain ⟨hjk, hrr⟩ := ih1 m'' c'' h
          refine ⟨by omega, ?_⟩
          rw [regRun_step_succ regProg m m' k hregstep]
          exact hjk ▸ hrr
        · intro hr
          obtain ⟨hjk, m_halt, hrun, hstep_halt⟩ := ih2 hr
          refine ⟨by omega, m_halt, ?_, hstep_halt⟩
          rw [regRun_step_succ regProg m m' j hregstep]
          exact hrun

/-- The elimination interpreter satisfies `Correct`. -/
theorem elimRun_correct : Correct elimRunNat := by
  intro prog n k hw hn
  simp only [elimRunNat]
  have hinv := allCandidates_invariant prog.toRegProg (RegMap.facmap n)
  set rex := elimRunExactAux (optTable prog.toRegProg) (allCandidates prog.toRegProg)
              (RegMap.facmap n) (allCandidates prog.toRegProg) k with hrex
  obtain ⟨r, j⟩ := rex
  have hspec := elimRunExactAux_correct prog.toRegProg k (RegMap.facmap n)
                  (allCandidates prog.toRegProg) hinv
  rw [← hrex] at hspec
  simp only at hspec
  obtain ⟨hsome, hnone⟩ := hspec
  cases hr : r with
  | none =>
    simp only [hr, Option.map_none]
    obtain ⟨_, m_halt, hrun, hstep⟩ := hnone hr
    refine ⟨RegMap.unfmap m_halt, ?_, ?_⟩
    · rw [regRun_eq prog n j hn hw, hrun]; rfl
    · have hwf_halt := regRun_wf prog (RegMap.facmap n) (RegMap.facmap_wf n) hw j m_halt hrun
      rw [← regStep_correct prog m_halt hwf_halt hw, hstep]; rfl
  | some mc =>
    obtain ⟨m', c'⟩ := mc
    simp only [hr, Option.map_some]
    obtain ⟨hjk, hrun⟩ := hsome m' c' hr
    refine ⟨by omega, ?_⟩
    rw [regRun_eq prog n j hn hw, hjk, hrun]; rfl

end Correctness
