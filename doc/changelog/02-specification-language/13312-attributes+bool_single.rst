- **Changed:**
  :term:`Boolean attributes <boolean attribute>` are now specified using
  key/value pairs, that is to say :n:`@ident__attr{? = {| on | off } }`.
  If the value is missing, the default is :n:`on`.  The old syntax is still
  supported, but produces the ``deprecated-attribute-syntax`` warning.

  Deprecated attributes are :attr:`universes(monomorphic)`,
  :attr:`universes(notemplate)` and :attr:`universes(noncumulative)`, which are
  respectively replaced by :attr:`universes(polymorphic=off) <universes(polymorphic)>`,
  :attr:`universes(template=off) <universes(template)>`
  and :attr:`universes(cumulative=off) <universes(cumulative)>`.
  Attributes :attr:`program` and :attr:`canonical` are also affected,
  with the syntax :n:`@ident__attr(false)` being deprecated in favor of
  :n:`@ident__attr=off`.

  (`#13312 <https://github.com/coq/coq/pull/13312>`_,
  by Emilio Jesus Gallego Arias).
