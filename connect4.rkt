#lang forge

sig Player {}
one sig P1 extends Player {}
one sig P2 extends Player {}

sig Index {inverse: set Index }
one sig A extends Index {}
one sig B extends Index {}
one sig C extends Index {}
one sig D extends Index {}

sig Board {places: set Index -> Index -> Player,
           first3: set Index,
           second3: set Index
}

pred wellformed4by4 {
  //constraints on sets
  Player = P1 + P2
  Index = A + B + C + D
  inverse = A->D + B->C + C->B + D->A
  first3 = A + B + C
  second3 = B + C + D

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



------------------win conditions------------------

//horizontal
pred winHf[b: Board, p: Player] {
  some r: Index | all c: b.first3 |
    p in b.places[r][c]
}
pred winHs[b: Board, p: Player] {
  some r: Index | all c: b.second3 |
    p in b.places[r][c]
}
pred winH[b: Board, p: Player] {
  winHf[b, p] or winHs[b, p]
}

//vertical
pred winVf[b: Board, p: Player] {
  some c: Index | all r: b.first3 |
    p in b.places[r][c]
}
pred winVs[b: Board, p: Player] {
  some c: Index | all r: b.second3 |
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

pred winning[b: Board, p: Player] {
  winH[b, p] or winV[b, p] or winD[b, p]
}

state[Board] initialBoard { no places }

transition[Board] move[p: Player, r: Index, c: Index] {
  -- this, this' are implicit: prestate and poststate
  -- 
  no places[r][c]             // <--- GUARD (only involves prestate)
  p = X => xturn[this]        // <--- GUARD (only involves prestate)
  p = O => oturn[this]        // <--- GUARD (only involves prestate)
  places' = places + r->c->p  // <--- ASSIGNMENT (poststate field = prestate expression)
    // ^ Assignment LHS is a field'
    //   Assignment RHS is the value of that field in this'
}