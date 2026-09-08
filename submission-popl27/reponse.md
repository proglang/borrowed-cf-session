Thanks to the reviewers for their thoughtful comments.

We first answer the specific questions of each reviewer,
and then comment on the rest.

## Review A

### why synchronization variables?
### explain the purity constraints discussed in 654-633
### 7.2 heuristic incompleteness


## Review A - detailed comments

### Polymorphic recursion

We never say polymorphic recursion is a problem. 
We just state that it is needed for resource-passing
style. In the context of a Hindley-Milner type system,
it would require type annotations as it would be rejected by
the standard algorithms.
In the System-F context, as in CFST, it does not matter because 
typing must be explicit.

