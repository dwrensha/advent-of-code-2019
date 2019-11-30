import system.io
open nat io

def hello_world : io unit :=
  put_str "hello world\n"

#eval hello_world


def print_squares : ℕ → io unit
| 0          := return ()
| (succ n)   := print_squares n >>
                put_str (to_string n ++ "^2 = " ++ to_string (n * n) ++ "\n")

#eval print_squares 100
