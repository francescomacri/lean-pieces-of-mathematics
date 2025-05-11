/- def hello := "world" -/
def main : IO Unit := IO.println "Hello, world!"

def add1 (n : Nat) : Nat := n + 1

/- Here the function add1 is called and the integer 7 is added -/
#eval add1 7

/- The same program, but with 7.0 being a folat: is not possible, because the function is defined with natural numbers -/
#eval add1 7

/- This is an addition of floats, returning floats. -/
#eval 1.2 + 2.8
