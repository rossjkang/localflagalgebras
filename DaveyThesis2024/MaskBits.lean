import Mathlib.Data.Nat.Bitwise

/-!
# Packing a predicate into a `Nat`, and reading it back

The τ-anchored family is enumerated over `Nat` masks, so C3 has to go the other
way: from a graph, produce the mask whose bits are its free-pair adjacencies.
`maskUpTo f n` packs the first `n` values of `f`, and `testBit_maskUpTo` reads
them back.

Deliberately in its own file with a single small import: the pentagon stack takes
minutes to load, and this is the kind of bit-fiddling that wants fast iteration.
-/

namespace Davey2024
namespace MaskBits

/-- Pack `f 0, …, f (n-1)` into the low `n` bits. -/
def maskUpTo (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (if f n then 1 <<< n else 0) ||| maskUpTo f n

/-- The packed value fits in `n` bits.  Needed because C2's enumeration ranges
over `mask < 2 ^ f`, so a mask recovered from a graph has to land inside it. -/
theorem maskUpTo_lt (f : Nat → Bool) : ∀ n, maskUpTo f n < 2 ^ n
  | 0 => by simp [maskUpTo]
  | n + 1 => by
    have ih := maskUpTo_lt f n
    have h1 : (if f n then (1 <<< n : Nat) else 0) < 2 ^ (n + 1) := by
      split
      · rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self n)
      · exact Nat.pow_pos (by omega)
    have h2 : maskUpTo f n < 2 ^ (n + 1) :=
      lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (by omega))
    exact Nat.or_lt_two_pow h1 h2

/-- The bit at index `i` of `if b then 2^n else 0`. -/
private theorem testBit_ite_two_pow (b : Bool) (n i : Nat) :
    (if b then (1 <<< n : Nat) else 0).testBit i = (b && decide (n = i)) := by
  cases b <;> simp [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

/-- Above the packed range every bit is clear.  Proved directly rather than
through a size bound, which needs arithmetic this does not. -/
theorem testBit_maskUpTo_high (f : Nat → Bool) :
    ∀ n i, n ≤ i → (maskUpTo f n).testBit i = false := by
  intro n
  induction n with
  | zero => intro i _; simp [maskUpTo]
  | succ m ih =>
    intro i hi
    simp only [maskUpTo, Nat.testBit_or, testBit_ite_two_pow, ih i (by omega),
      Bool.or_false]
    simp [show m ≠ i by omega]

/-- The packed bits read back. -/
theorem testBit_maskUpTo (f : Nat → Bool) :
    ∀ n i, i < n → (maskUpTo f n).testBit i = f i := by
  intro n
  induction n with
  | zero => intro i h; omega
  | succ m ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
    · simp only [maskUpTo, Nat.testBit_or, testBit_ite_two_pow, ih i h']
      simp [show m ≠ i by omega]
    · subst h'
      simp only [maskUpTo, Nat.testBit_or, testBit_ite_two_pow,
        testBit_maskUpTo_high f i i le_rfl, Bool.or_false]
      simp

#print axioms testBit_maskUpTo
#print axioms testBit_maskUpTo_high
#print axioms maskUpTo_lt

end MaskBits
end Davey2024
