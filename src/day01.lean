import system.io data.buffer.parser
open parser

def go {α} (file : string) (p : parser α) (m: α → option string) : io unit :=
do s ← io.fs.read_file file,
  sum.inr a ← return $ run p s,
  some str ← return $ m a,
  trace str (return ())

def parse_number := string.to_nat <$> many_char1 (sat char.is_digit)

def day1 := go "day01.txt" (many (parse_number <* ch '\n'))

def module_fuel (mass: ℤ) : ℤ := (int.div mass 3) - 2

def iter : list ℕ → ℤ → option string
| [] z := some $ to_string z
| (n::ns) z := iter ns ((module_fuel $ int.of_nat n) + z)

#eval day1 $ λ l, iter l 0


meta def module_total_fuel : ℤ → ℤ
| mass :=
  let f := module_fuel mass in
  if f ≤ 0 then 0
  else let subfuel := module_total_fuel f in
       subfuel + f


meta def iter2 : list ℕ → ℤ → option string
| [] z := some $ to_string z
| (n::ns) z := iter2 ns ((module_total_fuel $ int.of_nat n) + z)

#eval day1 $ λ l, iter2 l 0
