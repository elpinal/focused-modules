mlkit: make_lexer.sml make_parser.sml
	mlkit focused-modules-cli.mlb

mlton: make_lexer.sml make_parser.sml
	mlton -default-ann 'warnUnused true' focused-modules-cli.mlb

make_lexer.sml: make_lexer.cmlex
	cmlex -o make_lexer.sml make_lexer.cmlex

make_parser.sml: make_parser.cmyacc
	cmyacc -o make_parser.sml make_parser.cmyacc

.PHONY: mlkit mlton
