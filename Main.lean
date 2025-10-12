def main : IO Unit :=
  IO.println s!"Hello, hello!"

#check And
#check Or
#check Not

#check Prop
#check True
#check False
-- #check Proof

-- axiom and_comm' (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q r : Prop)
#check And p q
#check Or p q
