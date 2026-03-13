State and prove theorem 1 (label `thm:main`) in `informal_statements.tex` under the assumption of proposition 5.4 (label `\label{100}`) in `PRIME_VALUES_OF_RAMANUJAN_TAU_FUNCTION.tex`, that is:
For $X \in \mathbb{R}$, define
$$
S(X) := \#\{\ell ≤ X \mid \ell~\text{prime with}~|\tau(n)|=\ell ~\text{for some}~n\in\mathbb{N}\},
$$
where $\tau$ is the Ramanujan's tau function.

The task is to state and formalize the following statement:

The ABC-conjecture implies that as $X \to \infty$, we have
$$
S(X) = O(X^{\frac{9}{10}}\log(X)).
$$

Note that the task is **neither** proving ABC conjecture nor proposition 5.4, but prove a theorem **assuming** them.
That is,
```lean
def ABC : Prop := ...

def Proposition5_4 : Prop := ...

theorem ramanujan (h54 : Proposition5_4) (abc : ABC)  : ... := ...
```

Note that Xiong's proposition 5.4 and ABC conjecture need to be assumed throughout: 
for example the finiteness of $E_2$ and $E_4$ in `informal_statements` might requrie them.
