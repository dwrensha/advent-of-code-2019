import system.io data.buffer.parser
open parser nat

def go {α} (file : string) (p : parser α) (m: α → option string) : io unit :=
do s ← io.fs.read_file file,
  sum.inr a ← return $ run p s,
  some str ← return $ m a,
  trace str (return ())

inductive step
| right : ℕ → step
| left : ℕ → step
| up : ℕ → step
| down : ℕ → step


def parse_number : parser ℕ := string.to_nat <$> many_char1 (sat char.is_digit)

def parse_step : parser step :=
  do
    c ← one_of ['R', 'L', 'U', 'D'],
    n ← parse_number,
    return (match c with | 'R' := step.right n
                         | 'L' := step.left n
                         | 'U' := step.up n
                         | 'D' := step.down n
                         | _ := sorry
            end)



--def day03 := go "day03.txt" ((many (parse_number <* ch ',')) <* ch '\n')
