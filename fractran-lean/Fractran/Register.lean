import Fractran.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Basic


/-!
# Register-based FRACTRAN interpreter (Impl 2)

Represents the FRACTRAN state as a map from prime factors to exponents, using
`Std.TreeMap` for O(log n) lookup and update. A step becomes map arithmetic
(add numerator exponents, subtract denominator exponents) rather than big-integer
multiplication, avoiding redundant GCD/division work.

`RegMap` carries `Mul`, `Div`, and `One` instances so that fraction application
reads as `m / den * num`, mirroring the naive `n / q * p`. The homomorphism
lemmas (`unfmap_mul`, `unfmap_div`) are the core of the correctness proof.
-/

/-- Register map: maps primes to their exponents in the current FRACTRAN state.
    Primes absent from the map have exponent 0 by convention. -/
abbrev RegMap := Std.TreeMap ℕ ℕ compare

namespace RegMap

/-! ## Core operations -/

/-- Exponent of prime `p` in the map (0 if absent). -/
def get (m : RegMap) (p : ℕ) : ℕ := m.getD p 0

/-- Pointwise exponent addition — corresponds to multiplication of underlying numbers. -/
instance : Mul RegMap where
  mul m₁ m₂ := m₁.foldl (fun acc p e => acc.insert p (acc.get p + e)) m₂

/-- Empty map — corresponds to the number 1 (no prime factors). -/
instance : One RegMap where
  one := ∅

/-- Pointwise exponent subtraction (saturating) — corresponds to division.
    Keys that reach 0 are erased so zero-exponent primes are never stored. -/
instance : Div RegMap where
  div m₁ m₂ := m₂.foldl (fun acc p e =>
    let v := acc.get p - e
    if v = 0 then acc.erase p else acc.insert p v) m₁

/-- Build a `RegMap` from a natural number via its prime factorization.
    Uses `Nat.primeFactorsList` (sorted list with repetition) so insertion order is
    deterministic and zero-exponent primes are never stored. -/
def facmap (n : ℕ) : RegMap :=
  n.primeFactorsList.foldl (fun m p => m.insert p (m.get p + 1)) ∅

/-- Reconstruct the natural number from its register representation. -/
def unfmap (m : RegMap) : ℕ :=
  m.foldl (fun acc p e => acc * p ^ e) 1

/-- True iff every exponent in `den` is ≤ the corresponding exponent in `m`.
    Equivalent to: `unfmap den` divides `unfmap m`. -/
def applicable (den m : RegMap) : Bool :=
  den.all fun p e => m.get p ≥ e

/-- Apply fraction `(num, den)` to state `m`: divide out `den`, multiply in `num`. -/
def applyFrac (num den m : RegMap) : RegMap := m / den * num

/-! ## Bridge to Finsupp -/

/-- Convert a `RegMap` to a `Finsupp` for proof purposes.
    This is the key bridge: computation uses `TreeMap`, proofs use `Finsupp`. -/
noncomputable def toFinsupp (m : RegMap) : ℕ →₀ ℕ :=
  Finsupp.onFinset m.keys.toFinset (fun p => m.getD p 0) (by
    intro a ha
    rw [List.mem_toFinset, Std.TreeMap.mem_keys]
    by_contra h
    exact ha (Std.TreeMap.getD_eq_fallback h))

@[simp] lemma toFinsupp_apply (m : RegMap) (p : ℕ) :
    (toFinsupp m) p = m.getD p 0 := by
  simp [toFinsupp, Finsupp.onFinset_apply]

/-! ## TreeMap counting lemma -/

/-- Auxiliary: folding `insert p (getD p 0 + 1)` over a list counts occurrences. -/
private lemma count_foldl_aux (l : List ℕ) (m : RegMap) (p : ℕ) :
    (l.foldl (fun m q => m.insert q (m.getD q 0 + 1)) m).getD p 0 =
    m.getD p 0 + l.count p := by
  induction l generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, Std.TreeMap.getD_insert, List.count_cons]
    simp only [compare_eq_iff_eq]
    by_cases hxp : x = p
    · simp [hxp]; omega
    · simp [hxp]

/-- `facmap n` agrees with `Nat.factorization` pointwise. -/
lemma toFinsupp_facmap (n : ℕ) : toFinsupp (facmap n) = n.factorization := by
  ext p
  simp only [toFinsupp_apply, facmap, get, count_foldl_aux, Std.TreeMap.getD_emptyc]
  simp [Nat.primeFactorsList_count_eq]

/-! ## Homomorphism infrastructure -/

private lemma toList_empty : (∅ : RegMap).toList = [] := by
  have h1 := @Std.TreeMap.isEmpty_emptyc ℕ ℕ compare
  have h2 := @Std.TreeMap.isEmpty_toList ℕ ℕ compare ∅
  rw [h1] at h2; exact List.isEmpty_iff.mp h2

private lemma foldl_mul_map_prod {α : Type*} (l : List α) (f : α → ℕ) (init : ℕ) :
    l.foldl (fun acc x => acc * f x) init = init * (l.map f).prod := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

private lemma unfmap_eq_toList_prod (m : RegMap) :
    unfmap m = (m.toList.map (fun (p, e) => p ^ e)).prod := by
  simp only [unfmap, Std.TreeMap.foldl_eq_foldl_toList, foldl_mul_map_prod, one_mul]

lemma getD_of_mem_toList (m : RegMap) {p e : ℕ} (h : (p, e) ∈ m.toList) :
    m.getD p 0 = e := by
  have hmem := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp h
  rw [Std.TreeMap.getD_eq_getD_getElem?, hmem]; rfl

private lemma toList_prod_eq_keys_prod (m : RegMap) :
    (m.toList.map (fun (p, e) => p ^ e)).prod =
    m.keys.toFinset.prod (fun p => p ^ (m.getD p 0)) := by
  rw [List.prod_toFinset _ (Std.TreeMap.nodup_keys),
      ← Std.TreeMap.map_fst_toList_eq_keys, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ⟨p, e⟩ hmem
  simp only [Function.comp]
  congr 1; exact (getD_of_mem_toList m hmem).symm

private lemma keys_prod_eq_toFinsupp_prod (m : RegMap) :
    m.keys.toFinset.prod (fun p => p ^ (m.getD p 0)) =
    (toFinsupp m).prod (fun p e => p ^ e) := by
  rw [toFinsupp, Finsupp.onFinset_prod _ (by intro a; simp)]

/-- `unfmap` expressed via `Finsupp.prod` through the bridge. -/
lemma unfmap_eq_toFinsupp_prod (m : RegMap) :
    unfmap m = (toFinsupp m).prod (fun p e => p ^ e) := by
  rw [unfmap_eq_toList_prod, toList_prod_eq_keys_prod, keys_prod_eq_toFinsupp_prod]

/-! ## Homomorphism lemmas -/

@[simp] lemma unfmap_one : unfmap (1 : RegMap) = 1 := by
  change (∅ : RegMap).foldl (fun acc p e => acc * p ^ e) 1 = 1
  rw [Std.TreeMap.foldl_eq_foldl_toList, toList_empty]; simp

-- The conditional-add foldl separates initial value
private lemma foldl_cond_add_init (l : List (ℕ × ℕ)) (p : ℕ) (init : ℕ) :
    l.foldl (fun acc x => if x.1 = p then acc + x.2 else acc) init =
    init + l.foldl (fun acc x => if x.1 = p then acc + x.2 else acc) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons hd rest ih =>
    simp only [List.foldl_cons]
    by_cases hkp : hd.1 = p
    · simp only [hkp, ite_true]; rw [ih, ih (init := 0 + hd.2)]; omega
    · simp only [hkp, ite_false]; rw [ih]

-- TreeMap foldl insert-add preserves getD additively
private lemma foldl_insert_add_getD (l : List (ℕ × ℕ)) (m : RegMap) (p : ℕ) :
    (l.foldl (fun acc x => acc.insert x.1 (acc.getD x.1 0 + x.2)) m).getD p 0 =
    m.getD p 0 + l.foldl (fun acc x => if x.1 = p then acc + x.2 else acc) 0 := by
  induction l generalizing m with
  | nil => simp
  | cons hd rest ih =>
    simp only [List.foldl_cons]
    rw [ih, Std.TreeMap.getD_insert]
    simp only [compare_eq_iff_eq]
    by_cases hkp : hd.1 = p
    · simp only [hkp, ite_true, Nat.zero_add]
      rw [foldl_cond_add_init rest p hd.2]
      omega
    · simp [hkp]

-- Foldl over a list with no matching keys returns the initial value
private lemma foldl_cond_sum_none (l : List (ℕ × ℕ)) (p : ℕ) (init : ℕ)
    (h : p ∉ l.map Prod.fst) :
    l.foldl (fun acc x => if x.1 = p then acc + x.2 else acc) init = init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons, show hd.1 ≠ p from fun h' => h.1 (h'.symm), ite_false]
    exact ih _ h.2

-- The conditional foldl sum over toList extracts the entry for p
private lemma toList_foldl_sum_eq_getD (m : RegMap) (p : ℕ) :
    m.toList.foldl (fun acc x => if x.1 = p then acc + x.2 else acc) 0 = m.getD p 0 := by
  by_cases hp : p ∈ m
  · -- p is in the map: get value and find entry in toList
    have hget := Std.TreeMap.getElem?_eq_some_getD_of_contains
                   ((Std.TreeMap.contains_iff_mem).mpr hp) (fallback := 0)
    have hmem := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mpr hget
    -- Split the list around the matching entry
    obtain ⟨l₁, l₂, hlist⟩ := List.mem_iff_append.mp hmem
    -- p doesn't appear as a key in l₁ or l₂ (nodup)
    have hnodup : (m.toList.map Prod.fst).Nodup := by
      rw [Std.TreeMap.map_fst_toList_eq_keys]; exact Std.TreeMap.nodup_keys
    rw [hlist, List.map_append, List.map_cons] at hnodup
    -- Decompose nodup: l₁ keys disjoint from (p :: l₂ keys), and (p :: l₂ keys) is nodup
    rw [List.nodup_append] at hnodup
    obtain ⟨_, hnodup_r, hdisj⟩ := hnodup
    have hp1 : p ∉ l₁.map Prod.fst := by
      intro hmem
      exact absurd rfl (hdisj _ hmem p (List.mem_cons_self ..))
    have hp2 : p ∉ l₂.map Prod.fst :=
      (List.nodup_cons.mp hnodup_r).1
    -- Evaluate foldl: skip l₁, add v at (p, v), skip l₂
    rw [hlist, List.foldl_append, List.foldl_cons]
    rw [foldl_cond_sum_none l₁ p 0 hp1]
    simp only [ite_true, Nat.zero_add]
    rw [foldl_cond_sum_none l₂ p _ hp2]
  · -- p not in the map
    rw [Std.TreeMap.getD_eq_fallback hp]
    apply foldl_cond_sum_none
    rw [Std.TreeMap.map_fst_toList_eq_keys]
    exact fun hmem => hp (Std.TreeMap.mem_of_mem_keys hmem)

-- Pointwise: (m₁ * m₂).getD p 0 = m₁.getD p 0 + m₂.getD p 0
lemma mul_getD (m₁ m₂ : RegMap) (p : ℕ) :
    (m₁ * m₂).getD p 0 = m₁.getD p 0 + m₂.getD p 0 := by
  change (m₁.foldl (fun acc k v => acc.insert k (acc.getD k 0 + v)) m₂).getD p 0 = _
  rw [Std.TreeMap.foldl_eq_foldl_toList, foldl_insert_add_getD, toList_foldl_sum_eq_getD]
  omega

lemma toFinsupp_mul (m₁ m₂ : RegMap) :
    toFinsupp (m₁ * m₂) = toFinsupp m₁ + toFinsupp m₂ := by
  ext p; simp [mul_getD]

lemma unfmap_mul (m₁ m₂ : RegMap) : unfmap (m₁ * m₂) = unfmap m₁ * unfmap m₂ := by
  simp only [unfmap_eq_toFinsupp_prod, toFinsupp_mul]
  exact Finsupp.prod_add_index
    (by intro a _; simp) (by intro a _ b₁ b₂; exact pow_add a b₁ b₂)

lemma unfmap_facmap_eq_factorization_prod (n : ℕ) :
    unfmap (facmap n) = n.factorization.prod (fun p e => p ^ e) := by
  rw [unfmap_eq_toFinsupp_prod, toFinsupp_facmap]

/-- Round-trip: converting a positive natural to a register map and back is the identity. -/
lemma facmap_unfmap (n : ℕ) (hn : 0 < n) : unfmap (facmap n) = n := by
  rw [unfmap_facmap_eq_factorization_prod, Nat.prod_factorization_pow_eq_self hn.ne']

lemma applicable_eq_toList_all (den m : RegMap) :
    applicable den m = den.toList.all (fun (p, e) => decide (m.getD p 0 ≥ e)) := by
  simp only [applicable, get, Std.TreeMap.all, Std.DTreeMap.all,
             Std.DTreeMap.Internal.Impl.all_eq_all_toListModel,
             ← Std.DTreeMap.Internal.Impl.toList_eq_toListModel,
             Std.TreeMap.toList, Std.DTreeMap.Const.toList,
             Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map,
             List.all_map]
  congr 1

/-! ## Well-formedness: all keys are prime -/

/-- A RegMap is well-formed if all its keys are prime. This invariant is preserved
    by `Mul`, `Div`, and `applyFrac` when applied to `facmap`-images, and ensures
    that `unfmap` faithfully represents the map as a natural number. -/
def WF (m : RegMap) : Prop := ∀ p ∈ m, p.Prime

-- Keys of foldl insert over a list are contained in the list ∪ initial keys
private lemma foldl_insert_mem (l : List ℕ) (m : RegMap) (p : ℕ) :
    p ∈ l.foldl (fun m q => m.insert q (m.getD q 0 + 1)) m →
    p ∈ m ∨ p ∈ l := by
  induction l generalizing m with
  | nil => exact Or.inl
  | cons x xs ih =>
    intro hp
    -- After foldl_cons, the inner foldl starts from (m.insert x ...)
    rcases ih _ hp with hmem | hmem
    · -- p is in m.insert x (...)
      rw [Std.TreeMap.mem_insert] at hmem
      rcases hmem with ⟨hcmp⟩ | hmem
      · have := compare_eq_iff_eq.mp hcmp; exact Or.inr (List.mem_cons.mpr (Or.inl this.symm))
      · exact Or.inl hmem
    · exact Or.inr (List.mem_cons.mpr (Or.inr hmem))

lemma facmap_wf (n : ℕ) : WF (facmap n) := by
  intro p hp
  have := foldl_insert_mem n.primeFactorsList ∅ p hp
  rcases this with hempty | hmem
  · exact absurd hempty Std.TreeMap.not_mem_emptyc
  · exact Nat.prime_of_mem_primeFactorsList hmem

-- Foldl insert preserves WF if all inserted keys are prime
private lemma wf_foldl_insert (l : List (ℕ × ℕ)) (m : RegMap) (hm : WF m)
    (hl : ∀ x ∈ l, (x : ℕ × ℕ).1.Prime) :
    WF (l.foldl (fun acc x => acc.insert x.1 (acc.getD x.1 0 + x.2)) m) := by
  induction l generalizing m with
  | nil => exact hm
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro p hp
      rw [Std.TreeMap.mem_insert] at hp
      rcases hp with ⟨hcmp⟩ | hp
      · exact compare_eq_iff_eq.mp hcmp ▸ hl hd (List.mem_cons_self ..)
      · exact hm p hp
    · exact fun x hx => hl x (List.mem_cons.mpr (Or.inr hx))

lemma wf_mul (m₁ m₂ : RegMap) (h₁ : WF m₁) (h₂ : WF m₂) : WF (m₁ * m₂) := by
  change WF (m₁.foldl (fun acc p e => acc.insert p (acc.getD p 0 + e)) m₂)
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  apply wf_foldl_insert
  · exact h₂
  · intro ⟨p, e⟩ hmem
    have hget := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
    exact h₁ p (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by rw [hget]; rfl))

-- Foldl erase/insert preserves WF when only keys from the accumulator are modified
private lemma wf_foldl_div (l : List (ℕ × ℕ)) (m : RegMap) (hm : WF m) :
    WF (l.foldl (fun acc x =>
      let v := acc.getD x.1 0 - x.2
      if v = 0 then acc.erase x.1 else acc.insert x.1 v) m) := by
  induction l generalizing m with
  | nil => exact hm
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · -- erase case: keys are a subset
      intro p hp
      exact hm p (Std.TreeMap.mem_of_mem_erase hp)
    · -- insert case: only inserts existing key values
      intro p hp
      rw [Std.TreeMap.mem_insert] at hp
      rcases hp with ⟨hcmp⟩ | hp
      · exact hm _ (compare_eq_iff_eq.mp hcmp ▸ by
          by_contra hmem
          simp [Std.TreeMap.getD_eq_fallback hmem] at *)
      · exact hm p hp

lemma wf_div (m₁ m₂ : RegMap) (h₁ : WF m₁) : WF (m₁ / m₂) := by
  change WF (m₂.foldl (fun acc p e =>
    let v := acc.getD p 0 - e; if v = 0 then acc.erase p else acc.insert p v) m₁)
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  exact wf_foldl_div _ _ h₁

lemma wf_applyFrac (num den m : RegMap) (hnum : WF num) (hm : WF m) :
    WF (applyFrac num den m) := by
  exact wf_mul _ _ (wf_div m den hm) hnum

/-! ## Factorization bridge -/

private lemma unfmap_pos (m : RegMap) (hm : WF m) : 0 < unfmap m := by
  have h : unfmap m ≠ 0 := by
    rw [unfmap_eq_toFinsupp_prod, Finsupp.prod_ne_zero_iff]
    intro p hp
    apply pow_ne_zero
    have hsupp : (toFinsupp m) p ≠ 0 := Finsupp.mem_support_iff.mp hp
    simp only [toFinsupp_apply] at hsupp
    exact (hm p (by by_contra h'; exact hsupp (Std.TreeMap.getD_eq_fallback h'))).pos.ne'
  omega

private lemma factorization_unfmap_eq_toFinsupp (m : RegMap) (hm : WF m) :
    (unfmap m).factorization = toFinsupp m := by
  have hsupp_prime : ∀ p ∈ (toFinsupp m).support, p.Prime := fun p hp => by
    have hne : (toFinsupp m) p ≠ 0 := Finsupp.mem_support_iff.mp hp
    simp only [toFinsupp_apply] at hne
    exact hm p (by by_contra h; exact hne (Std.TreeMap.getD_eq_fallback h))
  rw [unfmap_eq_toFinsupp_prod]
  simp only [Finsupp.prod]
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hsupp_prime p hp).pos.ne'),
      Finset.sum_congr rfl (fun p hp => (hsupp_prime p hp).factorization_pow)]
  change (toFinsupp m).sum Finsupp.single = toFinsupp m
  exact Finsupp.sum_single (toFinsupp m)

/-! ## Divisibility ↔ applicable (for well-formed maps) -/

/-- For well-formed maps, `applicable den m` iff `unfmap den ∣ unfmap m`. -/
lemma applicable_iff_dvd (den m : RegMap) (hden : WF den) (hm : WF m) :
    applicable den m = true ↔ unfmap den ∣ unfmap m := by
  rw [← Nat.factorization_le_iff_dvd (unfmap_pos den hden).ne' (unfmap_pos m hm).ne',
      factorization_unfmap_eq_toFinsupp den hden,
      factorization_unfmap_eq_toFinsupp m hm, Finsupp.le_def]
  simp only [toFinsupp_apply]
  rw [applicable_eq_toList_all, List.all_eq_true]
  simp only [decide_eq_true_iff, ge_iff_le]
  constructor
  · intro h p
    by_cases hp : p ∈ den
    · have hmem : (p, den.getD p 0) ∈ den.toList :=
        (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mpr
          (Std.TreeMap.getElem?_eq_some_getD_of_contains
            (Std.TreeMap.contains_iff_mem.mpr hp))
      simpa using h ⟨p, den.getD p 0⟩ hmem
    · simp [Std.TreeMap.getD_eq_fallback hp]
  · intro h ⟨p, e⟩ hmem
    have he : den.getD p 0 = e := getD_of_mem_toList den hmem
    simpa [he] using h p

/-! ## Division homomorphism -/

-- Pointwise getD for the foldl underlying `Div`
private lemma foldl_div_getD (l : List (ℕ × ℕ)) (m : RegMap) (p : ℕ) :
    (l.foldl (fun acc x =>
      let v := acc.getD x.1 0 - x.2
      if v = 0 then acc.erase x.1 else acc.insert x.1 v) m).getD p 0 =
    m.getD p 0 - l.foldl (fun acc x => if x.1 = p then acc + x.2 else acc) 0 := by
  induction l generalizing m with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    -- Goal: step.getD p 0 - foldl_sum 0 tl = m.getD p 0 - foldl_sum (if ..) tl
    by_cases hkp : hd.1 = p
    · simp only [if_pos hkp, Nat.zero_add]
      -- RHS has foldl_sum hd.2 tl; rewrite to hd.2 + foldl_sum 0 tl
      conv_rhs => rw [foldl_cond_add_init]
      -- Goal: step.getD p 0 - tl_sum = m.getD p 0 - (hd.2 + tl_sum)
      by_cases hv : m.getD p 0 - hd.2 = 0
      · have hstep : (let v := m.getD hd.1 0 - hd.2
                      if v = 0 then m.erase hd.1 else m.insert hd.1 v).getD p 0 = 0 := by
          have hv' : m.getD hd.1 0 - hd.2 = 0 := by rw [hkp]; exact hv
          dsimp only; rw [hv', if_pos rfl, hkp, Std.TreeMap.getD_erase_self]
        rw [hstep, Nat.zero_sub]
        have hle : m.getD p 0 ≤ hd.2 := by omega
        exact (Nat.sub_eq_zero_of_le (le_trans hle (Nat.le_add_right _ _))).symm
      · have hstep : (let v := m.getD hd.1 0 - hd.2
                      if v = 0 then m.erase hd.1 else m.insert hd.1 v).getD p 0 =
                     m.getD p 0 - hd.2 := by
          have hv' : m.getD hd.1 0 - hd.2 ≠ 0 := by rw [hkp]; exact hv
          dsimp only; rw [if_neg hv', hkp, Std.TreeMap.getD_insert_self]
        rw [hstep, Nat.sub_sub]
    · simp only [if_neg hkp]
      -- foldl_sum 0 tl on both sides
      suffices h : (let v := m.getD hd.1 0 - hd.2
                    if v = 0 then m.erase hd.1 else m.insert hd.1 v).getD p 0 = m.getD p 0 by
        rw [h]
      dsimp only; split_ifs
      · rw [Std.TreeMap.getD_erase]
        simp only [compare_eq_iff_eq, show ¬(hd.1 = p) from hkp, ite_false]
      · rw [Std.TreeMap.getD_insert]
        simp only [compare_eq_iff_eq, show ¬(hd.1 = p) from hkp, ite_false]

-- (m / den).getD p 0 = m.getD p 0 - den.getD p 0
lemma div_getD (m den : RegMap) (p : ℕ) :
    (m / den).getD p 0 = m.getD p 0 - den.getD p 0 := by
  change (den.foldl (fun acc k e =>
    let v := acc.getD k 0 - e; if v = 0 then acc.erase k else acc.insert k v) m).getD p 0 =
    m.getD p 0 - den.getD p 0
  rw [Std.TreeMap.foldl_eq_foldl_toList, foldl_div_getD, toList_foldl_sum_eq_getD]

/-- Division in `RegMap` (pointwise exponent subtraction) corresponds to
    natural-number division, for well-formed maps when `den` is applicable. -/
lemma unfmap_div (m den : RegMap) (hm : WF m) (hden : WF den)
    (h : applicable den m = true) :
    unfmap (m / den) = unfmap m / unfmap den := by
  have hdvd := (applicable_iff_dvd den m hden hm).mp h
  have hpos_m := unfmap_pos m hm
  have hpos_den := unfmap_pos den hden
  have hpos_div : 0 < unfmap m / unfmap den :=
    Nat.div_pos (Nat.le_of_dvd hpos_m hdvd) hpos_den
  apply Nat.factorization_inj (unfmap_pos (m / den) (wf_div m den hm)).ne' hpos_div.ne'
  rw [factorization_unfmap_eq_toFinsupp (m / den) (wf_div m den hm),
      Nat.factorization_div hdvd,
      factorization_unfmap_eq_toFinsupp m hm,
      factorization_unfmap_eq_toFinsupp den hden]
  ext p
  simp only [Finsupp.tsub_apply, toFinsupp_apply]
  exact div_getD m den p

/-! ## Single-step correctness -/

/-- Applying `applyFrac` then `unfmap` matches naive fraction arithmetic,
    for well-formed maps. -/
lemma applyFrac_unfmap (num den m : RegMap) (hm : WF m) (hden : WF den)
    (h : applicable den m = true) :
    unfmap (applyFrac num den m) = unfmap m / unfmap den * unfmap num := by
  simp only [applyFrac, unfmap_mul, unfmap_div _ _ hm hden h]

end RegMap

/-! ## Positivity preservation -/

/-- A naive step on a positive state with a well-formed program yields a positive result. -/
lemma naiveStep_pos (prog : FractranProg) (n : ℕ) (hn : 0 < n) (hw : prog.WellFormed)
    (m : ℕ) (hm : naiveStep prog n = some m) : 0 < m := by
  simp only [naiveStep] at hm
  obtain ⟨l₁, ⟨p, q⟩, l₂, hlist, hfrac, _⟩ := List.findSome?_eq_some_iff.mp hm
  simp only at hfrac
  split_ifs at hfrac with hdvd
  · have heq := Option.some.inj hfrac; rw [← heq]
    have hmem : (p, q) ∈ prog := hlist ▸ List.mem_append_right _ (List.mem_cons_self ..)
    have ⟨hp, hq⟩ := hw _ hmem
    exact Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hn hdvd) hq) hp

/-- naiveRun preserves positivity under well-formed programs. -/
lemma naiveRun_pos (prog : FractranProg) (n : ℕ) (k : ℕ) (hn : 0 < n) (hw : prog.WellFormed)
    (m : ℕ) (hm : naiveRun prog n k = some m) : 0 < m := by
  induction k generalizing n m with
  | zero => simp [naiveRun] at hm; omega
  | succ k ih =>
    simp only [naiveRun] at hm
    match hk : naiveRun prog n k with
    | none => simp [hk] at hm
    | some n' =>
      simp only [hk] at hm
      exact naiveStep_pos prog n' (ih n hn n' hk) hw m hm

/-! ## Interpreter definitions -/

/-- Precompute the register representation of a `FractranProg` so factorizations
    are not repeated on every step. -/
def FractranProg.toRegProg (prog : FractranProg) : List (RegMap × RegMap) :=
  prog.map fun (p, q) => (RegMap.facmap p, RegMap.facmap q)

/-- One step of the register-based interpreter.
    Scans for the first fraction whose denominator is applicable and applies it. -/
def regStep (prog : List (RegMap × RegMap)) (m : RegMap) : Option RegMap :=
  prog.findSome? fun (num, den) =>
    if RegMap.applicable den m then some (RegMap.applyFrac num den m) else none

/-- Run the register interpreter for exactly `k` steps from state `m`.
    Returns `some m'` if still running after `k` steps, `none` if it halted earlier. -/
def regRun (prog : List (RegMap × RegMap)) (m : RegMap) : ℕ → Option RegMap
  | 0     => some m
  | k + 1 => regRun prog m k >>= regStep prog

/-- Nat-level wrapper around `regRun` conforming to the `Correct` interface.
    Returns `(result, k)` where `result` is the state option after `k` naive steps.
    For this impl `j = k` exactly (one naive step per internal step, no skipping). -/
def regRunNat (prog : FractranProg) (n k : ℕ) : Option ℕ × ℕ :=
  ((regRun prog.toRegProg (RegMap.facmap n) k).map RegMap.unfmap, k)

/-! ## Multi-step correctness -/

/-- One step of the register interpreter agrees with one naive step at the `ℕ` level,
    for well-formed maps and well-formed programs. -/
lemma regStep_correct (prog : FractranProg) (m : RegMap) (hm : RegMap.WF m)
    (hw : prog.WellFormed) :
    (regStep prog.toRegProg m).map RegMap.unfmap =
    naiveStep prog (RegMap.unfmap m) := by
  -- Both sides are findSome? over prog, with different per-element functions
  -- Both sides use findSome? over prog. Show they agree by induction on prog.
  simp only [regStep, naiveStep, FractranProg.toRegProg, List.findSome?_map]
  induction prog with
  | nil => simp
  | cons pq rest ih =>
    obtain ⟨p, q⟩ := pq
    simp only [List.findSome?_cons, Function.comp]
    have hpq := hw (p, q) (List.mem_cons_self ..)
    have hwrest : FractranProg.WellFormed rest :=
      fun x hx => hw x (List.mem_cons.mpr (Or.inr hx))
    -- Compare the if conditions: applicable (facmap q) m ↔ q ∣ unfmap m
    have hfq := RegMap.facmap_wf q
    have hconv : RegMap.applicable (RegMap.facmap q) m = true ↔ q ∣ RegMap.unfmap m := by
      rw [RegMap.applicable_iff_dvd _ _ hfq hm, RegMap.facmap_unfmap q hpq.2]
    by_cases happ : RegMap.applicable (RegMap.facmap q) m
    · -- Fraction fires
      have hdvd : q ∣ RegMap.unfmap m := hconv.mp happ
      simp only [happ, hdvd, ite_true, Option.map_some]
      rw [RegMap.applyFrac_unfmap _ _ _ hm hfq happ,
          RegMap.facmap_unfmap q hpq.2, RegMap.facmap_unfmap p hpq.1]
    · -- Fraction doesn't fire
      have hndvd : ¬ q ∣ RegMap.unfmap m := fun hdvd => happ (hconv.mpr hdvd)
      simp only [show RegMap.applicable (RegMap.facmap q) m = false from
        Bool.eq_false_iff.mpr happ, hndvd, ite_false]
      exact ih hwrest

/-- regStep preserves well-formedness. -/
lemma regStep_wf (prog : FractranProg) (m : RegMap) (hm : RegMap.WF m)
    (_ : prog.WellFormed) (m' : RegMap) (h : regStep prog.toRegProg m = some m') :
    RegMap.WF m' := by
  simp only [regStep, FractranProg.toRegProg, List.findSome?_map] at h
  obtain ⟨_, ⟨p, q⟩, _, _, hfrac, _⟩ := List.findSome?_eq_some_iff.mp h
  simp only [Function.comp] at hfrac
  split_ifs at hfrac with happ
  · have := Option.some.inj hfrac; rw [← this]
    exact RegMap.wf_applyFrac _ _ _ (RegMap.facmap_wf p) hm

/-- regRun preserves well-formedness. -/
lemma regRun_wf (prog : FractranProg) (m : RegMap) (hm : RegMap.WF m)
    (hw : prog.WellFormed) (k : ℕ) (m' : RegMap)
    (h : regRun prog.toRegProg m k = some m') : RegMap.WF m' := by
  induction k generalizing m m' with
  | zero => simp only [regRun] at h; exact (Option.some.inj h) ▸ hm
  | succ k ih =>
    simp only [regRun] at h
    match hk : regRun prog.toRegProg m k with
    | none => simp [hk] at h
    | some m'' =>
      simp only [hk] at h
      exact regStep_wf prog m'' (ih m hm m'' hk) hw m' h

/-- Register run agrees with naive run at every step count. -/
lemma regRun_eq (prog : FractranProg) (n k : ℕ) (hn : 0 < n) (hw : prog.WellFormed) :
    naiveRun prog n k =
    (regRun prog.toRegProg (RegMap.facmap n) k).map RegMap.unfmap := by
  -- Stronger induction: carry RegMap state and its WF through
  suffices h : ∀ (m : RegMap) (hm : RegMap.WF m),
      (regRun prog.toRegProg m k).map RegMap.unfmap =
      naiveRun prog (RegMap.unfmap m) k from by
    rw [h _ (RegMap.facmap_wf n), RegMap.facmap_unfmap n hn]
  intro m hm
  induction k generalizing m with
  | zero => simp [naiveRun, regRun]
  | succ k ih =>
    simp only [naiveRun, regRun]
    -- Use ih to get the relationship at step k
    have hih := ih m hm
    -- Case split on regRun result at step k
    cases hk : regRun prog.toRegProg m k with
    | none =>
      simp only [hk, Option.map_none] at hih
      -- hih : none = naiveRun prog (unfmap m) k
      -- Goal: (none >>= regStep ...).map unfmap = naiveRun ... k >>= naiveStep prog
      rw [← hih]; rfl
    | some m' =>
      simp only [hk, Option.map_some] at hih
      -- hih : some (unfmap m') = naiveRun prog (unfmap m) k
      -- Goal: (some m' >>= regStep ...).map unfmap = naiveRun ... k >>= naiveStep prog
      have hm' := regRun_wf prog m hm hw k m' hk
      rw [← hih]
      -- Goal: (some m' >>= regStep ...).map unfmap = some (unfmap m') >>= naiveStep prog
      -- Both sides: (regStep ... m').map unfmap = naiveStep prog (unfmap m')
      change (regStep prog.toRegProg m').map RegMap.unfmap = naiveStep prog (RegMap.unfmap m')
      exact regStep_correct prog m' hm' hw

/-- The register interpreter satisfies the `Correct` predicate.
    Requires well-formed programs and `0 < n` since `facmap 0 = ∅ = facmap 1`. -/
theorem regRun_correct : Correct regRunNat := by
  intro prog n k hw hn
  simp only [regRunNat]
  exact ⟨le_refl _, regRun_eq prog n k hn hw⟩
