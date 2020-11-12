- **Changed:**

  Boolean attributes are now specified using key/value pairs, that is
  to say ``attr={on,off}``. If the value is missing, the default is
  ``on``.  Old syntax is still supported, but produces the
  ``deprecated-attribute-syntax`` warning.

  Attributes deprecated are ``universes(monomorphic)``,
  ``universes(notemplate)``, ``universes(noncumulative)``, which are
  replaced by the corresponding ``universes(polymorphic=off)`` etc...
  Attributes :attr:`program` and :attr:`canonical` are also affected,
  with the syntax ``attr(false)`` being deprecated in favor of
  ``attr=off``.

  (`#13312 <https://github.com/coq/coq/pull/13312>`_,
  by Emilio Jesus Gallego Arias).
