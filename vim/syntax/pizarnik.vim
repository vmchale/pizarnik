scriptencoding utf-8

if exists('b:current_syntax')
    finish
endif

syntax match pizarnikComment "\v#.*$" contains=@Spell
syntax keyword pizarnikKeyword type
syntax keyword pizarnikBuiltin dup dip swap
syntax keyword pizarnikType Int Bool String
syntax keyword pizarnikVal True False
syntax match pizarnikName "\v[a-z][a-zA-Z0-9]*"
syntax match pizarnikTag "\v`[a-zA-Z][a-zA-Z0-9]*"
syntax match pizarnikSVar "\v'[A-Z][a-zA-Z0-9]*"
syntax match pizarnikType "\v[A-Z][a-zA-Z0-9]*"
syntax match pizarnikSymbol "&"
syntax match pizarnikSymbol "%-"
syntax match pizarnikSymbol "⁻¹"
syntax match pizarnikKeyword "@i"

highlight link pizarnikName Identifier
highlight link pizarnikComment Comment
highlight link pizarnikBuiltin Keyword
highlight link pizarnikType Type
highlight link pizarnikSVar Identifier
highlight link pizarnikSymbol Special
highlight link pizarnikKeyword Keyword
highlight link pizarnikVal Constant
highlight link pizarnikTag Constant

let b:current_syntax = 'pizarnik'
