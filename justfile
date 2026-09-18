default:
	@just --list

# Compile lean build
lean:
	cd lean && lake build

report CMD="pollux.pdf":
	cd latex && make {{CMD}}

# Run a command from the rocq Makefile
rocq CMD="check":
	cd rocq && make {{CMD}}
