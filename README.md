# tla-plus
playing along at home with Practical TLA+

## Values
```
Strings
"a", "b", "c"

Integers
1, 2, 3

Booleans
TRUE, FALSE
```
## Collections
```
Sets
{1, 2, 3}, {"a", "b", "c"}

Sequences/Tuples
<<1, "a", 2, "b", 3, "c">>
```
## Value Operations
```
Equals
x = y

Not Equals
x /= y
x # y

And
x /\ y

Or
x \/ y

Assignment (PlusCal only)
x := y

Not
~n
```
## Set Operations
```
All elements must be of the same type
{1, 2, 3}

Is element of set
x \in set

Is not element of set
x \notin set
~(x \in set)

Is subset of set
set1 \subseteq set2

Set union
set1 \union set2

Set Difference
set1 \ set2

Number of elements in set (requires EXTENDS FiniteSets)
Cardinality(set)

Power Set
SUBSET set

Set union
UNION set_of_sets

Cartesian product (not associative)
set1 \X set2
```

## Sequence / Tuple Operations
```
(all require EXTENDS Sequences)

Head
Head(seq)

Tail
Tail(seq)

Append
Append(seq, x)

Combine
seq1 \o seq2

Length
Len(seq)
```
