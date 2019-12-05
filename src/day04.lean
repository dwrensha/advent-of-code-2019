

def lower_bound : ℕ := 359282

def upper_bound : ℕ := 820401

def two_adjacent_digits_are_same : char → list char → bool
| _ [] := ff
| d (c::cs) := if c = d then tt else two_adjacent_digits_are_same c cs


def digits_never_decrease : char -> list char → bool
| _ [] := tt
| c (d::ds) := if c > d then ff else digits_never_decrease d ds

def is_good (n : ℕ) : bool :=
let cs : list char := (to_string n).data in
(two_adjacent_digits_are_same 'X' cs) && (digits_never_decrease '\n' cs)


meta def count_good_until (upper: ℕ) : ℕ → ℕ → ℕ
| current count :=
if current > upper then count
else let inc := if is_good current then 1 else 0
     in count_good_until (current + 1) (count + inc)


--#eval count_good_until upper_bound lower_bound 0

def exactly_two_adjacent_digits_are_same : char → char → char → list char → bool
| a b c [] := (b = c) && (a ≠ b)
| a b c (d::ds) := if (b = c) && (a ≠ b) && (c ≠ d) then tt else exactly_two_adjacent_digits_are_same b c d ds


def is_good2 (n : ℕ) : bool :=
let cs : list char := (to_string n).data in
(exactly_two_adjacent_digits_are_same 'X' 'Y' 'Z' cs) && (digits_never_decrease '\n' cs)


meta def count_good_until2 (upper: ℕ) : ℕ → ℕ → ℕ
| current count :=
if current > upper then count
else let inc := if is_good2 current then 1 else 0
     in count_good_until2 (current + 1) (count + inc)

#eval count_good_until2 upper_bound lower_bound 0
