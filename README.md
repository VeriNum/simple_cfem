# simple_cfem

This is a simple finite element code written in C for showing off
aspects of the method that the Verinum crew might be interested in
verifying with VST.  I would usually write this in other languages
(C++, Julia), but the VST toolchain mostly works with C.

The code is documented to be read, and the easiest way to get started is
the [documentation page](https://verinum.org/simple_cfem/) for this
repository.  If you have Lua, Quarto, and Coqdoc installed, you can build the
documents yourself: run `make doc`, which builds the documentation
Markdown from comments in the C files (via `util/ldoc.lua`) and then
converts it to a PDF and a web page (via Quarto).

See [ORGANIZATION.md](ORGANIZATION.md) for an outline of directory structure.
