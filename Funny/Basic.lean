def Filter (list : List α) : Type :=
  if list.length >= 1
  then Unit
  else Empty

def withNotEmpty (list : List α) (_ : Filter list) (f : List α → β) : β := f list

#eval withNotEmpty [1, 2, 3, 4] () List.sum
#eval withNotEmpty [] _ <| List.map (Nat.add 1)
