import system.io data.buffer.parser
open parser nat

def go {α} (file : string) (p : parser α) (m: α → option string) : io unit :=
do s ← io.fs.read_file file,
  sum.inr a ← return $ run p s,
  some str ← return $ m a,
  trace str (return ())

def parse_number := string.to_nat <$> many_char1 (sat char.is_digit)

def day1 := go "day02.txt" (many (parse_number <* ch ','))

lemma foo {n m : ℕ} (h: n ≤ m) (x : fin n) : x.val < m :=
let hx: x.val < n := x.is_lt in
lt_of_lt_of_le hx h

lemma le_plus_four {n : ℕ} : n ≤ n + 4 :=
less_than_or_equal.step $ less_than_or_equal.step $ less_than_or_equal.step $ less_than_or_equal.step $ less_than_or_equal.refl n

def coerce_fin {n m : ℕ} : ( n ≤ m ) → fin n → fin m
| hleq x := ⟨ x.val, foo hleq x ⟩

-- map current memory, current pointer, to new memory, and flag for done or not
def step (s: ℕ) : (array (s + 4) ℕ) → fin s → ((array (s + 4) ℕ) × bool)
| m idx :=
let current := m.read (coerce_fin le_plus_four idx)  in
if current = 99 then ⟨ m, true ⟩
else if current = 1 then sorry
else sorry


#check (⟨λ _, 0⟩: array 60 ℕ)


