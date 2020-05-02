#lang forge

-----------------------sigs-----------------------

sig Player {}
one sig X extends Player {}
one sig O extends Player {}
one sig Fill extends Player {}

sig Index {inverse: set Index,
           gravity: set Index}
one sig A extends Index {}
one sig B extends Index {}
one sig C extends Index {}
one sig D extends Index {}
one sig Bott extends Index {}

sig Board {places: set Index -> Index -> Player,
           first3: set Index,
           second3: set Index
}

----------------------setup-----------------------

pred wellformed4by4 {
  //constraints on sets
  Player = X + O + Fill
  Index = A + B + C + D + Bott
  inverse = A->D + B->C + C->B + D->A + Bott->Bott
  first3 = Board -> (A + B + C)
  second3 = Board -> (B + C + D)
  gravity = A->B + B->C + C->D + D->Bott + Bott->Bott

  //only one board position with its indices
  all b: Board | all r: Index | all c: Index | {
    lone r.(c.(b.places))    
  }
}

----------------------turns-----------------------

pred xturn[brd: Board] {
    #brd.places.X = #brd.places.O  
}

pred oturn[b: Board] { 
    subtract[#b.places.X,1] = #b.places.O
}

pred valid[b: Board] {
  oturn[b] or xturn[b]
}

------------------win conditions------------------

//horizontal
pred winHf[b: Board, p: Player] {
  some r: (Index - Bott) | all c: b.first3 |
    p in b.places[r][c]
}
pred winHs[b: Board, p: Player] {
  some r: (Index - Bott) | all c: b.second3 |
    p in b.places[r][c]
}
pred winH[b: Board, p: Player] {
  winHf[b, p] or winHs[b, p]
}

//vertical
pred winVf[b: Board, p: Player] {
  some c: (Index - Bott) | all r: b.first3 |
    p in b.places[r][c]
}
pred winVs[b: Board, p: Player] {
  some c: (Index - Bott) | all r: b.second3 |
    p in b.places[r][c]
}
pred winV[b: Board, p: Player] {
  winVf[b, p] or winVs[b, p]
}

//diagonal
pred winD[b: Board, p: Player] {
  (all i: b.first3 | i->i->p in b.places)
  or
  (all i: b.second3 | i->i->p in b.places)
  or
  (all i: b.first3 | i->i.inverse->p in b.places)
  or
  (all i: b.second3 | i->i.inverse->p in b.places)
}

//combined
pred winning[b: Board, p: Player] {
  winH[b, p] or winV[b, p] or winD[b, p]
}

state[Board] initialBoard {
    places = Bott -> A -> Fill +
             Bott -> B -> Fill +
             Bott -> C -> Fill +
             Bott -> D -> Fill
}

transition[Board] move[p: Player, r: Index, c: Index] {
  -- this, this' are implicit: prestate and poststate
  -- 
  no places[r][c]             // <--- GUARD (only involves prestate)
  one places[r.gravity][c] 
  p = X => xturn[this]        // <--- GUARD (only involves prestate)
  p = O => oturn[this]        // <--- GUARD (only involves prestate)
  
  
  places' = places + r->c->p  // <--- ASSIGNMENT (poststate field = prestate expression)
  first3' = first3
  second3' = second3
  
    // ^ Assignment LHS is a field'
    //   Assignment RHS is the value of that field in this'
}

transition[Board] game {
  some r: (Index - Bott) | some c: (Index - Bott) | some p: (Player - Fill)|
      move[this, this', p, r, c] -- FIX: we're discussing whether this, this' here should be implicit
}

trace<|Board, initialBoard, game, _|> T {}

run<|T|> {wellformed4by4 some p: (Player - Fill) | some b: Board | winning[b, p]} for exactly 6 Board