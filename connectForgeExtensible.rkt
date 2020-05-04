#lang forge

----------------Sigs----------------

sig Row {
    prev_row: lone Row,
    next_row: lone Row
}

sig Column {
    prev_col: lone Column,
    next_col: lone Column
}

sig Board {
    p1: set Row->Column,
    p2: set Row->Column
}

----------------Setup----------------

//Ensures the prev and next relations are properly formed for rows and columns
pred wellformed {
    one a: Row | no a.prev_row //First row has no previous
    one b: Row | no b.next_row //Last row has no next
    prev_row = ~next_row //Prev and next should be mirrored (transpose)
    all a: Row, b: Row | {
        //Any 2 distinct rows should be connected via prev or next
        not(a = b) implies (a in b.^prev_row) or (a in b.^next_row)
    }

    //Apply the same contrictions for columns
    one a: Column | no a.prev_col
    one b: Column | no b.next_col
    prev_col = ~next_col
    all a: Column, b: Column | {
        not(a = b) implies (a in b.^prev_col) or (a in b.^next_col)
    }

    //Two players cannot have played the same index
    no Board.p1 & Board.p2
}

----------------Turns----------------

//p1's turn if both players have the same # of moves
pred p1_turn[b: Board] {
    #(b.p1) = #(b.p2)
}

//p2's turn, p1 is always within one move
pred p2_turn[b: Board] {
    subtract[#(b.p1),1] = #(b.p2)
}

//always a player's turn, no extra turns
pred valid[b: Board] {
    p1_turn[b] or p2_turn[b]
}

----------------Win Cons----------------

//Checks if given player has won vertically
pred vertical_w[p: set Row->Column] {
    //Look for 3 distinct, vertically adjacent indices for given player
    some x,y,z: Row | some c: Column | {
        not x = y
        not x = z
        not y = z
        (x->c + y->c + z->c) in p
        x.prev_row = y
        y.prev_row = z
    }
}

//Checks if given player has won horizontally
pred horizontal_w[p: set Row->Column] {
    //Look for 3 distinct, horizontally adjacent indices for given player
    some r: Row | some x,y,z: Column | {
        not x = y
        not x = z
        not y = z
        (r->x + r->y + r->z) in p
        x.next_col = y
        y.next_col = z
    }
}

//Checks if given player has won diagonally
pred diagonal_w[p: set Row->Column] {
    //Look for distinct, diagonally adjacent indices for given player
    some a,b,c: Row | some x,y,z: Column | {
        not a = b
        not a = c
        not b = c
        not x = y
        not x = z
        not y = z
        (a->x + b->y + c->z) in p
        a.prev_row = b
        b.prev_row = c
        x.next_col = y
        y.next_col = z
    }
}

//Combined win conditions
pred won[p: set Row->Column] {
    vertical_w[p] or diagonal_w[p] or horizontal_w[p]
}

//Either p1 or p2 wins
pred finished[b: Board] {
    won[b.p1] or won[b.p2]
}

//Check if p1 can win
pred p1_canwin[b: Board] {
    //Look for index at (r,c) such that:
    some r: Row | some c: Column | {
        //Available space
        not r->c in b.p1 + b.p2
        //Bottom row or has a piece below it
        some r.prev_row implies r.prev_row->c in b.p1 + b.p2
        //Allows p1 to win the game
        won[b.p1 + r->c]
    }
}

//Check if p2 can win
pred p2_canwin[b: Board] {
    some r: Row | some c: Column | {
        not r->c in b.p1 + b.p2
        some r.prev_row implies r.prev_row->c in b.p1 + b.p2
        won[b.p2 + r->c]
    }
}

--------------------Win/Turn Tests---------------------

inst boiler {
  Board = Board0
  Row = Row0 + Row1 + Row2 + Row3
  Column = Column0 + Column1 + Column2 + Column3
  next_row = Row0 -> Row1 + Row1 -> Row2 + Row2 -> Row3
  prev_row = Row3 -> Row2 + Row2 -> Row1 + Row1 -> Row0
  next_col = Column0 -> Column1 + Column1 -> Column2 + Column2 -> Column3
  prev_col = Column3 -> Column2 + Column2 -> Column1 + Column1 -> Column0
}

inst emptyGame {
  boiler
  p1 = none
  p2 = none
}

//Empty game checks
expect {
    wfEmpty1: {wellformed} for exactly emptyGame is sat
    wfEmpty2: {not wellformed} for exactly emptyGame is unsat    
}

//Horizontal win
inst horizontal {
    boiler
    p1 = Board -> (Row3 -> Column0 + Row2 -> Column0 + Row2 -> Column1)
    p2 = Board -> (Row3 -> Column1 + Row3 -> Column2 + Row3 -> Column3)
}

//Vertical win
inst vertical {
    boiler
    p1 = Board -> (Row3 -> Column0 + Row2 -> Column0 + Row1 -> Column0)
    p2 = Board -> (Row3 -> Column1 + Row3 -> Column2)
}

//Diagonal win
inst diagonal {
    boiler
    p1 = Board -> (Row3 -> Column1 + Row3 -> Column2 + Row2 -> Column2)
    p2 = Board -> (Row3 -> Column0 + Row2 -> Column1 + Row1 -> Column2)
}

//Uneven turns
inst moreX {
    boiler
    p1 = Board -> (Row3 -> Column0 + Row2 -> Column0 + Row2 -> Column1)
    p2 = Board -> (Row3 -> Column1)
}

//Win tests
expect {
    //well formed
    wellformed: {wellformed} for exactly horizontal is sat
    //all tests either show positive win, or unsat if not
    ht: {won[Board.p2]} for exactly horizontal is sat
    hf: {vertical_w[Board.p1]} for exactly horizontal is unsat
    vt: {won[Board.p1]} for exactly vertical is sat
    vf: {won[Board.p2]} for exactly vertical is unsat
    dt: {won[Board.p2]} for exactly diagonal is sat
}

//Turn tests
expect {
    //turns are correct for given conditions
    valid: {valid[Board]} for exactly horizontal is sat
    p1: {p1_turn[Board]} for exactly horizontal is sat
    p2: {p2_turn[Board]} for exactly horizontal is unsat
    //turns are incorrect, extra turn for p1
    moreX: {p1_turn[Board] or p2_turn[Board]} for exactly moreX is unsat
    noWin: {won[Board.p1] or won[Board.p2]} for exactly moreX is unsat
}

----------------Trace----------------

//Define initial state of the game, no pieces
state[Board] initialBoard {
    no p1
    no p2
}

//Initial starts in center
state[Board] centerStart {
    one a: Row | no a.prev_row and a in p1.Column 
    one b: Column | no b.prev_col and b.next_col in Row.p1 
    #p1 = 1
    no p2
}

//Initial starts in left corner
state[Board] cornerStart {
    one a: Row | no a.prev_row and a in p1.Column 
    one b: Column | no b.prev_col and b in Row.p1 
    #p1 = 1
    no p2
}

//Setup so p1 can win next turn, two p1 and two p2 horizontally layered on
//top of each other
state[Board] proofStart {
      some a: (Row - Row.^next_row) | some b: (Column - Column.^next_col) | {
          (a -> b + a -> b.next_col) in p1
          (a.next_row -> b + a.next_row -> b.next_col) in p2
          #p1 = 2
          #p2 = 2
      }
}

//Define parameters for transitioning (making a move)
transition[Board] move[r: Row, c: Column] {
    //Move being made on an empty index
    not r->c in (p1 + p2)

    //if r is not the bottom row, there must already be a move below r->c
    some r.prev_row implies (r.prev_row)->c in (p1 + p2) //GRAVITY
    
    //Player whose turn it is gets r->c
    p1_turn[this] implies {
        p1' = p1 + r->c
        p2' = p2
    }
    p2_turn[this] implies {
        p2' = p2 + r->c
        p1' = p1
    }

    //Game cannot already have been won
    not finished[this]
}

//No gravity
transition[Board] moveZeroGrav[r: Row, c: Column] {
    not r->c in (p1 + p2)
   
    p1_turn[this] implies {
        p1' = p1 + r->c
        p2' = p2
    }
    p2_turn[this] implies {
        p2' = p2 + r->c
        p1' = p1
    }
    
    not finished[this]
}

//Same transition as "move" but players will move to win if they can
transition[Board] moveIntel[r: Row, c: Column] {
    not r->c in (p1 + p2)

    some r.prev_row implies (r.prev_row)->c in (p1 + p2)
    
    p1_turn[this] implies {
        p1' = p1 + r->c
        p2' = p2
        //If p1 can make a move to win, they must do so
        p1_canwin[this] implies won[p1']
    }
    p2_turn[this] implies {
        p2' = p2 + r->c
        p1' = p1
        //If p2 can make a move to win, they must do so
        p2_canwin[this] implies won[p2']
    }

    not finished[this]
}

//random moves
transition[Board] game {
    some r: Row | some c: Column | move[this, this', r, c]
}

//moves can be placed anywhere, won't "fall"
transition[Board] gameZeroGrav {
    some r: Row | some c: Column | moveZeroGrav[this, this', r, c]
}

//players end games if option available
transition[Board] gameIntel {
    some r: Row | some c: Column | moveIntel[this, this', r, c]
}

trace<|Board, initialBoard, game, _|> Pure {} //start anywhere, random moves
trace<|Board, centerStart, game, _|> CenterStartPure {} //start center, random moves
trace<|Board, cornerStart, game, _|> CornerStartPure {} //start left corner, random moves
trace<|Board, proofStart, gameIntel, _|> ProofStartIntel  {} //start in proof scenario, intelligent moves

//We only used the above traces for our testing, but you can make traces for any combination
//of game type, dimension, starting point, and move parameters.

-------------------Trace Tests-----------------------

//run {wellformed} for exactly 4 Row, exactly 4 Column, exactly 1 Board
//run<|Pure|> {wellformed some b: Board | finished[b]} for exactly 3 Row, exactly 3 Column, exactly 6 Board
//run<|centerStartPure|> {wellformed some b: Board | finished[b]} for exactly 3 Row, exactly 3 Column, exactly 6 Board
//run<|CornerStartPure|> {wellformed some b: Board | won[b.p1]} for exactly 3 Row, exactly 3 Column, exactly 6 Board

//A test demonstrating that the intelligent move will always  finish the board, and never allow p2 to win
expect {
    alwayswin: <|ProofStartIntel|> {wellformed some b: Board | won[b.p2]} for exactly 3 Row, exactly 3 Column, 4 Board is unsat
    alwayswinopp: <|ProofStartIntel|> {wellformed some b: Board | won[b.p1]} for exactly 3 Row, exactly 3 Column, 4 Board is sat
}