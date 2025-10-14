cabal run pc -- repl lib/maybe.piz prelude/fn.piz
2
drop

I guess because the new state lexer treats 'drop' using lib/maybe.piz aliases instead of updating?
or because prelude/fn is inducted using its own, while repl state expects whatever started with lib/maybe.piz...
