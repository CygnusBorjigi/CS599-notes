


# Imperative Language

## Syntax

For this simple language, there are two basic types of expressions and one type of commands, arithmetic expression and boolean expression. 

#### arithmetic expression

The arithmetic expression can be one of the following:
1. A Number : takes in a natural number
2. A ID : takes in a string
3. An addition operation : takes in two other arithmetic expression
4. A subtraction operation : takes in two other arithmetic expression
5. A multiplication : takes in two other arithmetic expression

Defined as following

```coq
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)  
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
```

#### boolean expression

The boolean expression can be one of the following:

1. The equivalence of a boolean true : takes in nothing
2. The equivalence of a boolean false : takes in nothing
3. Check the equivalency between two arithmetic operations : takes in two arithmetic operations
4. Check if one arithmetic operation evaluate to a value that is less than another value evaluated to by another arithmetic operation : takes in two arithmetic operations.
5. The equivalence of a boolean negation : takes in a boolean expression
6. The equivalence of a boolean and : takes in two boolean expressions

Defined as following:

```coq
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
```

#### commands

There are $5$ possible commands in the stack programming language.

1. Skip command : takes in no input
2. Assign command : takes in a string and a arithmetic expression as input
3. Bind command : takes in two other commands
4. Conditional command ; takes in a boolean expression and two other commands
5. While loop : takes in a boolean expression and a command

```coq
Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
```

## Evaluation

To evaluate the expression, there are also two `fixpoint` functions, one for each type of expressions.


#### Arithmetic expression

In order to evaluate arithmetic expression, we break them down into each individual cases:

1. Arithmetic numbers: simply take the numbers out of the constructor
2. Arithmetic ID: takes the string out of the constructor and input it into the `total_map` to get the value associated with that ID
3. Arithmetic addition: call the evaluation recursively for each of the two arithmetic expression with the current memory and add the evaluation result.
4. Arithmetic subtraction: call the evaluation recursively for each of the two arithmetic expression with the current memory and subtract the result of the right side from the left side.
5. Arithmetic multiplication: call the evaluation recursively for each of the two arithmetic expression with the current memory and multiply the result.

```coq
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.
```

#### boolean operation

For boolean operation, we do the same:

1. The equivalence of true : evaluate to boolean true
2. The equivalence of false : evaluate to boolean false
3.  Check the equivalency between two arithmetic operations : call the arithmetic evaluation function on both sides and check for equality
4. Check if one arithmetic operation evaluate to a value that is less than another value evaluated to by another arithmetic operation : call the arithmetic evaluation and check for the lesser than relation
5. The equivalence of a boolean negation : evaluate the boolean expression using the current `state` and negate the result.
6. The equivalence of a boolean and : recursively call the boolean evaluation function on each side independently using the current `state` and evaluate the conjunction of those two result.

```coq
Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.
```

#### empty state

For this chapter, we define the empty state as a total map where the default is `0`

```coq
  Definition empty_st := (_ !-> 0).
```

## Operational Semantics

#### Skip command

```
            -----------------
            st =[ skip ]=> st
```

#### Assign command

```
            aeval st a = n
        -------------------------------
        st = [ x := a ] => (x !-> n ; st)
```

Takes the value `a` assign it to name `x`, and associate `x` to ID `n` in total map `st`

#### Bind command 

```
               st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           
                         st =[ c1;c2 ]=> st''
```

Takes in two commands and apply them one after the other.

#### Conditional command true

```
               beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               
                st =[ if b then c1 else c2 end ]=> st'
```

Assuming expression `b` will evaluate to true using the current memory, the command will evaluate the memory using command `c1`

#### Conditional command false

```
                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              
                st =[ if b then c1 else c2 end ]=> st'
```

Assuming expression `b` will evaluate to false using the current memory, the command will evaluate the memory using command `c2`

#### While loop terminate

```
                         beval st b = false
                    -----------------------------                 
                    st =[ while b do c end ]=> st
```

Assuming expression `b` will evaluate to false using the current memory, the command out put the current memory

#### While loop continue

```
                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------         
                  st  =[ while b do c end ]=> st''
```

Assuming expression `b` will evaluate to true using the current memory, the command will evaluate the memory using command `c`

```coq
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').
```
