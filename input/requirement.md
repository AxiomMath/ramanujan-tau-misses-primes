1. ABC conjecture and Xiong's proposition 5.4 (label `\label{100}`) in `PRIME_VALUES_OF_RAMANUJAN_TAU_FUNCTION.tex` should be assumed whenever necessary. Here, "necessary" means if assuming ABC conjecture and proposition 5.4 can greatly simplify the proof and avoid formalising deep results such as Siegel's theorem.

That is, formalizations need to dependend on ABC or proposition 5.4 whenever necessary:
```lean
def ABC : Prop := ...

def Proposition5_4 : Prop := ...

theorem some_theorem (h54 : Proposition5_4) (abc : ABC)  : ... := ...
```

2. When formalizing ramanujan's $\tau$ function, we use predicate instead of concrete definitions. We will assume $\tau$ is a function satisfying 
- Hecke multiplicativity and recurrence
- Parity
- Deligne's bound
- Non-unit property
