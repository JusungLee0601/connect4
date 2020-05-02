#lang forge

-----------------------sigs-----------------------

//Players:
//Fill exists as a way to catch the "bottom" of the board, isn't
//necessary for a no gravity game
sig Player {}
one sig X extends Player {}
one sig O extends Player {}
one sig Fill extends Player {}

//Index:
//Basics for a 4 by 4 board but can be limited by constraining Index in
//wellformed variants, Bott is the index for the bottom row, again only
//necessary for gravity
sig Index {inverse: set Index,
           gravity: set Index}
one sig A extends Index {}
one sig B extends Index {}
one sig C extends Index {}
one sig D extends Index {}
one sig Bott extends Index {}

//Board:
//Places allows for Players in certain spots on the board, first3 and second3
//are used for a 3 connect, are not flexible to rule changes!
sig Board {places: set Index -> Index -> Player,
           first3: set Index,
           second3: set Index
}

----------------------setup-----------------------

//Basic constraints
pred wellformed4by4 {
  //constraints on sets
  Player = X + O + Fill
  Index = A + B + C + D + Bott
  inverse = A->D + B->C + C->B + D->A + Bott->Bott
  //used as references in the win predicates
  first3 = Board -> (A + B + C)
  second3 = Board -> (B + C + D)
  //pieces can fall down by matching against the index directly below
  gravity = A->B + B->C + C->D + D->Bott + Bott->Bott

  //only one board position with its indices
  all b: Board | all r: Index | all c: Index | {
    lone r.(c.(b.places))    
  }
}

----------------------turns-----------------------

//Makes sure no more than one "piece" is placed between transitions
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

//Horizontal:
//Must check that wins occur either along ABC or BCD columns, as it can be
//either on a 4 by 4 board with a connect 3 condition, cannot include
//Bott or else will match against filled in bottom row
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

//Vertical:
//The same as above, except now ABC or BCD rows
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

//Diagonal
pred winD[b: Board, p: Player] {
  (all i: b.first3 | i->i->p in b.places)
  or
  (all i: b.second3 | i->i->p in b.places)
  or
  (all i: b.first3 | i->i.inverse->p in b.places)
  or
  (all i: b.second3 | i->i.inverse->p in b.places)
}

//Combined
pred winning[b: Board, p: Player] {
  winH[b, p] or winV[b, p] or winD[b, p]
}

--------------------trace setup-------------------

//Intial Board:
//Includes the "bottom", a row with spots taken by player "Fill" so placed
//pieces can check to see if the piece below it is occupied
state[Board] initialBoard {
    places = Bott -> A -> Fill +
             Bott -> B -> Fill +
             Bott -> C -> Fill +
             Bott -> D -> Fill
}

transition[Board] move[p: Player, r: Index, c: Index] {
  -- this, this' are implicit: prestate and poststate
  //no pieces in the spot being placed
  no places[r][c]            
  //one piece in the spot directly below
  one places[r.gravity][c]
  //no extra pieces placed, turns are being taken at the right time
  p = X => xturn[this]        
  p = O => oturn[this]        
  
  //before and after must be correct
  places' = places + r->c->p 
  first3' = first3
  second3' = second3
}

//This is specifically constrained such that only non Fill players can place
//in non Bott positions so we can still play within the original 4 by 4, ABCD
//board
transition[Board] game {
  some r: (Index - Bott) | some c: (Index - Bott) | some p: (Player - Fill)|
      move[this, this', p, r, c] -- FIX: we're discussing whether this, this' here should be implicit
}

----------------------traces----------------------

trace<|Board, initialBoard, game, _|> T {}

//This needs the 6 board specification to not be unsat
run<|T|> {wellformed4by4 some p: (Player - Fill) | some b: Board | winning[b, p]} for exactly 6 Board