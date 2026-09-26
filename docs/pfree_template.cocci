@freeing@
type rt, t;
identifier f, i;
position p;
@@
rt f(..., t i, ...) {
<+...
pfree@p(i)
...+>
}

@script:python@
f << freeing.f;
t << freeing.t;
@@
print(f"Function : {f}")
print(f"Parameter type : {t}")
