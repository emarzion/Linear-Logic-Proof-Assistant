# Linear-Logic-Proof-Assistant
Sequent calculus based proof assistant for ILL

Based off the following presentation of ILL: http://llwiki.ens-lyon.fr/mediawiki/index.php/Intuitionistic_linear_logic

The language of ILL is defined as follows (each binary operation is right-associative, from greatest-to-lowest precedence):

    formula ::=  P
                |0
                |1
                |Tr
                |!formula
                |formula * formula
                |formula & formula
                |formula + formula
                |formula -o formula

## Sequents

The general proof context is a list of sequents which keep track of everything that you still need to prove, along with your available assumptions.

Generally, a sequent looks like

    H1 : P1
    .
    .
    .
    Hn : Pn
    _______
    Q

In this example, `Q` is the goal to be proved and `P1,...,Pn` are the assumptions which are allowed to be used.  `H1,...,Hn` are the respective names assigned to these assumptions.

## Proofs

To begin a proof of a formula , enter "Theorem" followed by that formula.  For instance, `Theorem P -o P` will generate the sequent with `P -o P` as a goal and no assumptions:

    _______
    P -o P

The goals and sequencts can be modified using tactics:

**`id` tactic**

Enter `id` when the top sequence is of the form:

    H : A

    _______

    A

This sequent is then removed.

**`one` tactic**

Enter `one` when the goal is `1` and there are no assumptions:

    _______
    1
    
 This sequent is consequently removed.
 
 **`true` tactic**
 
 Enter `true` when the goal is `Tr`:
 
     ...
     _______
     Tr
 
 This sequent is then removed.
