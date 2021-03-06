mlkit: make_lexer.sml make_parser.sml
	mlkit --output focused-modules-mlkit focused-modules-cli.mlb

mlton: make_lexer.sml make_parser.sml
	mlton -output focused-modules-mlton -default-ann 'warnUnused true' -default-ann 'allowExtendedTextConsts true' focused-modules-cli.mlb

make_lexer.sml: make_lexer.cmlex
	cmlex -o make_lexer.sml make_lexer.cmlex

make_parser.sml: make_parser.cmyacc
	cmyacc -o make_parser.sml make_parser.cmyacc

.PHONY: mlkit mlton
