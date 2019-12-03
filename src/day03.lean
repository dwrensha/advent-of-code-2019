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
    trace ((to_string c) ++ (to_string n)) (return ()),
    return (match c with | 'R' := step.right n
                         | 'L' := step.left n
                         | 'U' := step.up n
                         | 'D' := step.down n
                         | _ := sorry
            end)

def parse_wires : parser (list step × list step) :=
  do
   wire1 ← sep_by (ch ',') parse_step,
   ch '\n',
   wire2 ← sep_by (ch ',') parse_step,
   return ⟨wire1, wire2⟩

def day03 := go "day03.txt" parse_wires

#eval day03 $ λ _, some "SUCCESS"
