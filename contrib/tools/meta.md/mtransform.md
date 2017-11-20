Module Transformations
======================

This file is a collection of the module transformations available for Maude.

Removing Conditional Equations/Rules
------------------------------------

```maude
fmod UNCONDITIONALIZE is
   protecting META-LEVEL .

    vars T T' C' : Term . var AS : AttrSet . var C : Condition . var V : Variable .
    var H : Header . var IL : ImportList . var SS : SortSet .
    var SSDS : SubsortDeclSet . var OPDS : OpDeclSet . var MAS : MembAxSet .
    var EQS : EquationSet . var RLS : RuleSet . var FM : FModule .

    --- TODO: Implement/use some existing implementation.
    op varAway : TermList -> Variable .
    -----------------------------------

    op internalizeConditions : RuleSet -> [RuleSet] .
    op internalizeConditions : Module  -> [Module]  .
    -------------------------------------------------
    eq internalizeConditions(none) = none .
    eq internalizeConditions( rl T => T'      [AS] . RLS) = (rl      T     =>      T'                [AS] .) internalizeConditions(RLS) .
   ceq internalizeConditions(crl T => T' if C [AS] . RLS) = (rl '_|_[T, V] => '_|_[T', '_/\_[V, C']] [AS] .) internalizeConditions(RLS)
    if C' := upTerm(C)
    /\ V  := varAway((T,T',C')) .

    eq internalizeConditions(FM) = FM .
    eq internalizeConditions(mod H is IL sorts SS . SSDS OPDS MAS EQS RLS endm)
     = (mod H is IL sorts SS . SSDS OPDS MAS EQS internalizeConditions(RLS) endm) .
endfm
```