``` hidden
module substructural_logic where
```

# Substructural Logic

A substructural logic is a logic which lacks one or more of the
traditional structural rules (i.e. contraction, weakening and
exchange[^exch]).
Discarding contraction and weakening makes logics *resource
sensitive* [@girard1987; @girard1995].
Discarding exchange makes logics *order sensitive*.


## Applications in programming language theory

Most of the work on substructural logics in relation to programming
language theory is in the field of linear type theory, where the
linear properties of the type system are exploited to allow explicit
de-allocation, in-place re-use of memory, more efficient garbage
collection or safe parallelism
[see @plasmeijer2002; @turner1999; @igarashi2000; @bernardy2015].

Some additional work has been done in the field of ordered type
theory, where the order sensitivity of the calculus is used to achieve
even more efficient memory management [see @petersen2003].


[^exch]: Exchange can be take apart into the rules of commutativity
         and associativity for the structural operator(s).
