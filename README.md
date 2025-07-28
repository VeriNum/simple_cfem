# simple_cfem

This is a simple finite element code written in C for showing off
aspects of the method that the Verinum crew might be interested in
verifying with VST.  I would usually write this in other languages
(C++, Julia), but the VST toolchain mostly works with C.

If you have Lua and Quarto installed, the easiest way to get a feel
for the code is to run `make doc`, which builds the documentation
Markdown from comments in the C files (via `util/ldoc.lua`) and then
converts it to a PDF and a web page (via Quarto).

