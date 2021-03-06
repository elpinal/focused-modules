# Focused-modules

An implementation of a type system for ML-style modules proposed by [Crary 2020] in Standard ML.
[Crary 2020] solves the avoidance problem, a problem related to abstract types and scoping, by ideas from focused logic.

## Getting started

You need a Standard ML compiler ([MLKit](http://elsman.com/mlkit/) or [MLton](http://mlton.org)) and [`cmtool`](http://www.cs.cmu.edu/~crary/cmtool/).
Make sure that `mlkit` (or `mlton`), `cmlex` and `cmyacc` are in your `$PATH`.

```
$ git clone --recursive https://github.com/elpinal/focused-modules
$ cd focused-modules
```

### Build with MLKit

```
$ make
$ ./focused-modules-mlkit
```

### Build with MLton

```
$ make mlton
$ ./focused-modules-mlton
```

## Syntax

The syntax is what is described in the paper, extended with let-binding for ordinary modules.

- Supports n-ary lambda abstraction at term, type and module level.
- Supports shorthand `M` for `'a/M` when `'a` does not occur free in the scope.
- Supports non-dependent versions of functions and products.
- Supports boolean and integer literals.

## References
### A focused solution to the avoidance problem

Karl Crary.  
Journal of Functional Programming, 30, e24, 2020.  
http://www.cs.cmu.edu/~crary/papers/2020/exsig.pdf

### Extensional equivalence and singleton types

Christopher A. Stone and Robert Harper.  
ACM Transactions on Computational Logic 7(4), 676–722, 2006.  
http://www.cs.cmu.edu/~rwh/papers/singletons/tocl.pdf
