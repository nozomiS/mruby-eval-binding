mruby-eval-binding
==================

mruby-eval-binding is a forked version of mruby-eval in mruby, further,
which provides an object of class Binding.
Also it may provide some perfomance improvements.

### Methods

See mruby-eval and,

Kernel#binding

Binding#eval
Binding#local_variable_defined?
Binding#local_variable_get
Binding#local_variable_set
Binding#local_variables
Binding#receiver

### Limitation

Up to 127 local variables are allowed for addition but it depends on
rest of stack of VM.
Because this implementation consumes the stack for all env's local varaibles and additonal local variables.

### License

MIT
