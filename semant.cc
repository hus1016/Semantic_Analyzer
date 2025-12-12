#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
extern int semant_debug;
extern char *curr_filename;
//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol
arg,
arg2,
Bool,
concat,
cool_abort,
copy,
Int,
in_int,
in_string,
IO,
length,
Main,
main_meth,
No_class,
No_type,
Object,
out_int,
out_string,
prim_slot,
self,
SELF_TYPE,
Str,
str_field,
substr,
type_name,
val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
arg         = idtable.add_string("arg");
arg2        = idtable.add_string("arg2");
Bool        = idtable.add_string("Bool");
concat      = idtable.add_string("concat");
cool_abort  = idtable.add_string("abort");
copy        = idtable.add_string("copy");
Int         = idtable.add_string("Int");
in_int      = idtable.add_string("in_int");
in_string   = idtable.add_string("in_string");
IO          = idtable.add_string("IO");
length      = idtable.add_string("length");
Main        = idtable.add_string("Main");
main_meth   = idtable.add_string("main");
//   _no_class is a symbol that can't be the name of any
//   user-defined class.
No_class    = idtable.add_string("_no_class");
No_type     = idtable.add_string("_no_type");
Object      = idtable.add_string("Object");
out_int     = idtable.add_string("out_int");
out_string  = idtable.add_string("out_string");
prim_slot   = idtable.add_string("_prim_slot");
self        = idtable.add_string("self");
SELF_TYPE   = idtable.add_string("SELF_TYPE");
Str         = idtable.add_string("String");
str_field   = idtable.add_string("_str_field");
substr      = idtable.add_string("substr");
type_name   = idtable.add_string("type_name");
val         = idtable.add_string("_val");
}
ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {
/* Add basic classes first to construct the inheritance graph */
install_basic_classes();
/* Then add the remaining classes */
for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
add_to_class_table(classes->nth(i));
}
}
void ClassTable::install_basic_classes() {
// The tree package uses these globals to annotate the classes built below.
// curr_lineno  = 0;
Symbol filename = stringtable.add_string("<basic class>");
// The following demonstrates how to create dummy parse trees to
// refer to basic Cool classes.  There's no need for method
// bodies -- these are already built into the runtime system.
// IMPORTANT: The results of the following expressions are
// stored in local variables.  You will want to do something
// with those variables at the end of this method to make this
// code meaningful.
//
// The Object class has no parent class. Its methods are
//        abort() : Object    aborts the program
//        type_name() : Str   returns a string representation of class name
//        copy() : SELF_TYPE  returns a copy of the object
//
// There is no need for method bodies in the basic classes---these
// are already built in to the runtime system.
Class_ Object_class =
class_(Object,
No_class,
append_Features(
append_Features(
single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
filename);
//
// The IO class inherits from Object. Its methods are
//        out_string(Str) : SELF_TYPE       writes a string to the output
//        out_int(Int) : SELF_TYPE            "    an int    "  "     "
//        in_string() : Str                 reads a string from the input
//        in_int() : Int                      "   an int     "  "     "
//
Class_ IO_class =
class_(IO,
Object,
append_Features(
append_Features(
append_Features(
single_Features(method(out_string, single_Formals(formal(arg, Str)),
SELF_TYPE, no_expr())),
single_Features(method(out_int, single_Formals(formal(arg, Int)),
SELF_TYPE, no_expr()))),
single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
filename);
//
// The Int class has no methods and only a single attribute, the
// "val" for the integer.
//
Class_ Int_class =
class_(Int,
Object,
single_Features(attr(val, prim_slot, no_expr())),
filename);
//
// Bool also has only the "val" slot.
//
Class_ Bool_class =
class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);
//
// The class Str has a number of slots and operations:
//       val                                  the length of the string
//       str_field                            the string itself
//       length() : Int                       returns length of the string
//       concat(arg: Str) : Str               performs string concatenation
//       substr(arg: Int, arg2: Int): Str     substring selection
//
Class_ Str_class =
class_(Str,
Object,
append_Features(
append_Features(
append_Features(
append_Features(
single_Features(attr(val, Int, no_expr())),
single_Features(attr(str_field, prim_slot, no_expr()))),
single_Features(method(length, nil_Formals(), Int, no_expr()))),
single_Features(method(concat,
single_Formals(formal(arg, Str)),
Str,
no_expr()))),
single_Features(method(substr,
append_Formals(single_Formals(formal(arg, Int)),
single_Formals(formal(arg2, Int))),
Str,
no_expr()))),
filename);
add_to_class_table(Object_class);
add_to_class_table(IO_class);
add_to_class_table(Int_class);
add_to_class_table(Bool_class);
add_to_class_table(Str_class);
}
////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////
ostream& ClassTable::semant_error(Class_ c)
{
return semant_error(c->get_filename(),c);
}
ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
error_stream << filename << ":" << t->get_line_number() << ": ";
return semant_error();
}
ostream& ClassTable::semant_error()
{
semant_errors++;
return error_stream;
}
/*

Other ClassTable methods
*/

/*

Adds the class to the class table (specifically, adds it to the class map
and the inheritance graph) with the following caveats:

Cannot add a class that has already been defined.


Classes cannot inherit from Bool, SELF_TYPE, or String.


Cannot define a SELF_TYPE class.
*/
void ClassTable::add_to_class_table(Class_ c) {
Symbol name = c->get_name();
Symbol parent = c->get_parent();
if (class_map.count(name) > 0 || inheritance_graph.count(name) > 0) {
ostream& err_stream = semant_error(c);
err_stream << "Class " << name << " has already been defined.\n";
}
else if (parent == Bool || parent == Str || parent == SELF_TYPE) {
ostream& err_stream = semant_error(c);
err_stream << "Class " << name << " cannot inherit class " << parent << ".\n";
}
else if (name == SELF_TYPE) {
ostream& err_stream = semant_error(c);
err_stream << "Redefinition of basic class " << name << ".\n";
}
else {
class_map[name] = c;
inheritance_graph[name] = parent;
}
}


/*

Validates the inheritance graph by checking that:

Every parent class is defined.


There are no cycles.


The class Main is defined.
*/
bool ClassTable::is_valid() {
bool is_main_defined = false;
std::map<Symbol, Symbol>::iterator iter = inheritance_graph.begin();
while (iter != inheritance_graph.end()) {
Symbol child = iter->first;
Symbol parent = iter->second;
if (child == Main) {
is_main_defined = true;
}
Symbol current = parent;
while (current != No_class) {
if (current == child) {
ostream& err_stream = semant_error(class_map[child]);
err_stream << "Class " << child << " inherits from itself.\n";
return false;
}
if (inheritance_graph.find(current) == inheritance_graph.end()) {
ostream& err_stream = semant_error(class_map[child]);
err_stream << "Class " << child << " inherits from undefined class "
<< parent << ".\n";
return false;
}
current = inheritance_graph[current];
}
++iter;
}
if (is_main_defined == false) {
ostream& err_stream = semant_error();
err_stream << "Class Main is not defined.\n";
return false;
}
return true;
}


/*

Returns the least upper bound (least common ancestor)
of classes class1 and class2) in the inheritance graph.
This is a naive O(N^2) algorithm where N is the branch
length.
*/
Symbol ClassTable::lub(Symbol class1, Symbol class2) {
Symbol c1 = class1;
Symbol lub_result = Object;
do {
Symbol c2 = class2;
do {
if (c1 == c2) {
lub_result = c1;
return lub_result;
}
c2 = inheritance_graph[c2];
} while (c2 != Object);
c1 = inheritance_graph[c1];
} while (c1 != Object);
return lub_result;
}

/*

Returns true if child is a subclass of parent, false otherwise.
This is an O(N) algorithm where N is the branch length.
*/
bool ClassTable::is_child(Symbol child, Symbol parent) {
if (parent == Object) return true;
Symbol current = child;
do {
if (current == parent) return true;
current = inheritance_graph[current];
} while (current != Object);
return false;
}

bool ClassTable::class_exists(Symbol c) {
return inheritance_graph.find(c) != inheritance_graph.end();
}
Class_ ClassTable::get_class(Symbol class_name) {
return class_map[class_name];
}
/*

Traverses the inheritance chain of the input class until
it finds a method matching the input method name and returns
the corresponding formal parameters. Returns NULL if no matching
method is found.
*/
Formals ClassTable::get_formals(Symbol class_name, Symbol method_name) {
Symbol current_name = class_name;
do {
Class_ current_class = class_map[current_name];
Formals formals_list = current_class->get_formals(method_name);
if (formals_list != NULL) return formals_list;
current_name = inheritance_graph[current_name];
} while (current_name != No_class);
return NULL;
}

/*

Traverses the inheritance chain of the input class until
it finds a method matching the input method name and returns
the corresponding formal parameters. Returns NULL if no matching
method is found.
*/
Symbol ClassTable::get_return_type(Symbol class_name, Symbol method_name) {
Symbol current_name = class_name;
do {
Class_ current_class = class_map[current_name];
Symbol ret_type = current_class->get_return_type(method_name);
if (ret_type != NULL) return ret_type;
current_name = inheritance_graph[current_name];
} while (current_name != No_class);
return NULL;
}

/*

Traverses the inheritance chain of the input class, starting with
the parent, until it finds a method matching the input method name
and returns the corresponding class name. Returns NULL if no matching
method is found. This is a kind of hacky solution that uses get_return_type,
which works because get_return_type <=> method exists in that class.
*/
Symbol ClassTable::get_ancestor_method_class(Symbol class_name, Symbol method_name) {
Symbol current_name = inheritance_graph[class_name];
do {
Class_ current_class = class_map[current_name];
if (current_class->get_return_type(method_name) != NULL)
return current_class->get_name();
current_name = inheritance_graph[current_name];
} while (current_name != No_class);
return NULL;
}

/*

Checks the method signature of the input method for the two classes.
Returns true if the signatures are the same; specifically, if the
following hold:

Formal parameters have the same types in the same order


Number of formal parameters are the same


Return types match

Does NOT ensure that the formal parameters have the same identifiers.
*/
bool ClassTable::check_method_signature(Symbol c1, Symbol c2, Symbol method_name) {
Class_ cls1 = class_map[c1];
Class_ cls2 = class_map[c2];
Formals formals1 = cls1->get_formals(method_name);
Formals formals2 = cls2->get_formals(method_name);
Symbol return1 = cls1->get_return_type(method_name);
Symbol return2 = cls2->get_return_type(method_name);
if (return1 != return2) return false;
int idx1 = formals1->first();
int idx2 = formals2->first();
while (formals1->more(idx1) && formals2->more(idx2)) {
if (formals1->nth(idx1)->get_type() != formals2->nth(idx2)->get_type())
return false;
idx1 = formals1->next(idx1);
idx2 = formals2->next(idx2);
}
return !(formals1->more(idx1) || formals2->more(idx2));
}

/*   This is the entry point to the semantic checker.
Your checker should do the following two things:

Check that the program is semantically correct
Decorate the abstract syntax tree with type information
by setting the type' field in each Expression node. (see tree.h')

You are free to first do 1), make sure you catch all semantic
errors. Part 2) can be done in a second stage, when you want
to build mycoolc.
*/
void program_class::semant()
{
initialize_constants();
/* Initialize a new ClassTable inheritance graph and make sure it
is well-formed. */
ClassTable *classtable = new ClassTable(classes);
if (classtable->is_valid() && !classtable->errors()) {
type_env_t env;
env.om = new SymbolTable<Symbol, Symbol>();
env.curr = NULL;
env.ct = classtable;
/* Recursively type check each class. */
int idx = classes->first();
while (classes->more(idx)) {
env.om->enterscope();
env.curr = classes->nth(idx);
classes->nth(idx)->init_class(env); // So the attributes are global
// in the class environment/scope
classes->nth(idx)->type_check(env);
env.om->exitscope();
idx = classes->next(idx);
}
}
if (classtable->errors()) {
cerr << "Compilation halted due to static semantic errors." << endl;
exit(1);
}
}
/*

Other semantic analysis helper methods defined in cool-tree.h.
*/

Symbol class__class::get_name() {
return name;
}
Symbol class__class::get_parent() {
return parent;
}
/*

Initializes environment tables with class attributes.
Adds class attributes along the inheritance change,
adding parent class attributes first.
*/
void class__class::init_class(type_env_t env) {
if (name == Object) return;
env.ct->get_class(parent)->init_class(env);
int feat_idx = features->first();
while (features->more(feat_idx)) {
features->nth(feat_idx)->add_to_environment(env);
feat_idx = features->next(feat_idx);
}
}

/*

Gets the list of formals for a particular method of the class.
Returns NULL if the method isn't found.
*/
Formals class__class::get_formals(Symbol method) {
int feat_idx = features->first();
while (features->more(feat_idx)) {
Feature feature = features->nth(feat_idx);
if (feature->is_method() && feature->get_name() == method)
return feature->get_formals();
feat_idx = features->next(feat_idx);
}
return NULL;
}

/*

Gets the return type of a particular method of the class.
Returns NULL if the method isn't found.
*/
Symbol class__class::get_return_type(Symbol method) {
int feat_idx = features->first();
while (features->more(feat_idx)) {
Feature feature = features->nth(feat_idx);
if (feature->is_method() && feature->get_name() == method)
return feature->get_return_type();
feat_idx = features->next(feat_idx);
}
return NULL;
}

/*

Simple accessors for classes defined in cool-tree.h.
*/
bool method_class::is_method() { return true; }
bool attr_class::is_method() { return false; }

Formals method_class::get_formals() { return formals; }
Symbol method_class::get_return_type() { return return_type; }
// These two methods should never be called.
Formals attr_class::get_formals() { return NULL; }
Symbol attr_class::get_return_type() { return NULL; }
Symbol method_class::get_name() { return name; };
Symbol attr_class::get_name() { return name; };
void method_class::add_to_environment(type_env_t env) { /* Nothing to do */ }
void attr_class::add_to_environment(type_env_t env) {
if (env.om->probe(name) != NULL) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Unable to add attribute " << name
<< " to object map (already defined).\n";
} else {
env.om->addid(name, &type_decl);
}
}
Symbol formal_class::get_type() { return type_decl; }
Symbol branch_class::get_type() { return type_decl; }
/*

Top-most step in recursive type checking. Recursively checks each of the
features (methods and attributes). Does not impose any type restrictions.
*/
Class_ class__class::type_check(type_env_t env) {
int feat_idx = features->first();
while (features->more(feat_idx)) {
features->nth(feat_idx)->type_check(env);
feat_idx = features->next(feat_idx);
}
return this;
}

/*

Recursively checks formal parameters for the method as follows:

In a new environment scope, bind the keyword self.


Recursively check the formal parameters in this environment.


For the resulting parameter types:


If the method is inherited, make sure the ancestor method is properly overwritten.


Declared return value of SELF_TYPE should return SELF_TYPE.


Make sure the return type is a defined class (exists in the class table).


Make sure the return type is a subtype of the declared return type.
*/
Feature method_class::type_check(type_env_t env) {
env.om->enterscope();
Symbol current_class = env.curr->get_name();
env.om->addid(self, &current_class);
int formal_idx = formals->first();
while (formals->more(formal_idx)) {
formals->nth(formal_idx)->type_check(env);
formal_idx = formals->next(formal_idx);
}
Symbol inferred_ret = expr->type_check(env)->type;


Symbol ancestor_class = env.ct->get_ancestor_method_class(current_class, name);
if (ancestor_class != NULL && !env.ct->check_method_signature(ancestor_class, current_class, name)) {
ostream &err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Overriding method signature of " << name << " for class "
<< current_class << " doesn't match method signature for ancestor "
<< ancestor_class << ".\n";
}
if (!env.ct->class_exists(return_type)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Undefined return type " << return_type << " in method " << name << ".\n";
} else if (return_type == SELF_TYPE) {
if (inferred_ret != SELF_TYPE) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Inferred return type " << inferred_ret << " of method " << name
<< " does not conform to declared return type " << return_type << ".\n";
}
} else {
Symbol adjusted_inferred = (inferred_ret == SELF_TYPE) ? env.curr->get_name() : inferred_ret;
if (!env.ct->is_child(adjusted_inferred, return_type)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Method initialization " << inferred_ret
<< " is not a subclass of " << return_type << ".\n";
}
}
env.om->exitscope();
return this;
}
/*

Type checks a class attribute as follows:

In a new environment scope, bind the keyword self.


Evaluate the initialization of the attribute.


Make sure the initialized type is a subclass of the declared type.
*/
Feature attr_class::type_check(type_env_t env) {
if (name == self) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "'self' cannot be the name of an attribute.\n";
}
env.om->enterscope();
Symbol current_class = env.curr->get_name();
env.om->addid(self, &current_class);
Symbol init_type = init->type_check(env)->type;
env.om->exitscope();
Symbol adjusted_init = (init_type == SELF_TYPE) ? env.curr->get_name() : init_type;
if (init_type != No_type && !env.ct->is_child(adjusted_init, type_decl)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Attribute initialization " << init_type
<< " is not a subclass of " << type_decl << ".\n";
}
return this;
}


/*

Type checks a formal parameter by making sure it hasn't already been defined in the
current scope.
*/
Formal formal_class::type_check(type_env_t env) {
if (env.om->probe(name) != NULL) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Duplicate formal " << name << ".\n";
} else if (type_decl == SELF_TYPE) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Formal parameter " << name << " cannot have type SELF_TYPE\n";
} else {
env.om->addid(name, &type_decl);
}
return this;
}

/* Adds the branch to the environment. See typcase_class for more details. */
Symbol branch_class::type_check(type_env_t env) {
// The following condition should never be true because a branch identifier
// is the first thing initialized in its own scope. This is just a sanity check.
if (env.om->probe(name) == NULL) {
env.om->addid(name, &type_decl);
} else {
ostream &err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Identifier " << name << " already defined in current scope.\n";
return Object;
}
return expr->type_check(env)->type;
}
/*

Adds the identifier to the environment after checking its evaulated type
and making sure that's a subclass of the declared type.
*/
Expression assign_class::type_check(type_env_t env) {
Symbol var_type = *env.om->lookup(name);
Symbol expr_type = expr->type_check(env)->type;
if (expr_type == SELF_TYPE) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Cannot assign to 'self'.\n";
type = Object;
} else if (!env.ct->is_child(expr_type, var_type)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << expr_type << " is not a subclass of " << var_type << ".\n";
type = Object;
} else {
type = expr_type;
}
return this;
}

/*

Same as normal dispatch (see dispatch_class::type_check(type_env_t env) below),
with the additional condition that the evaluated type of the calling expression e
must be a subtype of the static class T in e@T.f(...).
*/
Expression static_dispatch_class::type_check(type_env_t env) {
Symbol receiver_type = expr->type_check(env)->type;
if (receiver_type == SELF_TYPE) receiver_type = env.curr->get_name();
if (!env.ct->is_child(receiver_type, type_name)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Evaluated class " << receiver_type << " must be a child of declared class "
<< type_name << " in static dispatch.\n";
type = Object;
return this;
}
std::vector<Symbol> param_types;
int actual_idx = actual->first();
while (actual->more(actual_idx)) {
Symbol param_type = actual->nth(actual_idx)->type_check(env)->type;
if (param_type == SELF_TYPE) param_type = env.curr->get_name();
param_types.push_back(param_type);
actual_idx = actual->next(actual_idx);
}
Formals declared_formals = env.ct->get_formals(receiver_type, name);
Symbol declared_ret = env.ct->get_return_type(receiver_type, name);
if (declared_formals == NULL || declared_ret == NULL) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Dispatch to undefined method " << name << ".\n";
type = Object;
return this;
}
std::vector<Symbol>::iterator param_iter = param_types.begin();
int formal_idx = declared_formals->first();
while (param_iter != param_types.end() && declared_formals->more(formal_idx)) {
Symbol eval_param = *param_iter;
Symbol decl_param = declared_formals->nth(formal_idx)->get_type();
if (decl_param == SELF_TYPE) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Formal parameter cannot have type SELF_TYPE.\n";
} else if (!env.ct->is_child(eval_param, decl_param)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Formal parameter declared type " << decl_param
<< " is not a subclass of " << eval_param << ".\n";
}
++param_iter;
formal_idx = declared_formals->next(formal_idx);
}
if (param_iter != param_types.end() || declared_formals->more(formal_idx)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Number of declared formals doesn't match number checked.\n";
}
type = (declared_ret == SELF_TYPE) ? receiver_type : declared_ret;
return this;
}

/*

Given the following expression: e.f(e1, ..., en), performs the following check:

Recursively checks e.


Recursively checks e1, ..., en.


Makes sure that the evaluated types of e1, ..., en are subtypes of the types

declared in the method signature.

Returns:


The evaluated type if the declared type is SELF_TYPE.


The declared type otherwise.
*/
Expression dispatch_class::type_check(type_env_t env) {
Symbol receiver_type = expr->type_check(env)->type;
Symbol dispatch_class = receiver_type;
if (receiver_type == SELF_TYPE) dispatch_class = env.curr->get_name();
std::vector<Symbol> param_types;
int actual_idx = actual->first();
while (actual->more(actual_idx)) {
Symbol param_type = actual->nth(actual_idx)->type_check(env)->type;
if (param_type == SELF_TYPE) param_type = env.curr->get_name();
param_types.push_back(param_type);
actual_idx = actual->next(actual_idx);
}
Formals declared_formals = env.ct->get_formals(dispatch_class, name);
Symbol declared_ret = env.ct->get_return_type(dispatch_class, name);
if (declared_formals == NULL || declared_ret == NULL) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Dispatch to undefined method " << name << ".\n";
type = Object;
return this;
}
std::vector<Symbol>::iterator param_iter = param_types.begin();
int formal_idx = declared_formals->first();
while (param_iter != param_types.end() && declared_formals->more(formal_idx)) {
Symbol eval_param = *param_iter;
Symbol decl_param = declared_formals->nth(formal_idx)->get_type();
if (decl_param == SELF_TYPE) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Formal parameter cannot have type SELF_TYPE.\n";
} else if (!env.ct->is_child(eval_param, decl_param)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Formal parameter declared type " << decl_param
<< " is not a subclass of " << eval_param << ".\n";
}
++param_iter;
formal_idx = declared_formals->next(formal_idx);
}
if (param_iter != param_types.end() || declared_formals->more(formal_idx)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Number of declared formals doesn't match number checked.\n";
}
type = (declared_ret == SELF_TYPE) ? receiver_type : declared_ret;
return this;
}


/*

Recursively type checks the predicate, then the then expression, then the
else expression. Makes sure the predicate evaluates to Bool and returns
the least upper bound of the types of the other two expressions.
*/
Expression cond_class::type_check(type_env_t env) {
Symbol pred_type = pred->type_check(env)->type;
Symbol then_type = then_exp->type_check(env)->type;
if (then_type == SELF_TYPE) then_type = env.curr->get_name();
Symbol else_type = else_exp->type_check(env)->type;
if (else_type == SELF_TYPE) else_type = env.curr->get_name();
if (pred_type != Bool) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "If condition did not evaluate to a boolean.\n";
type = Object;
} else {
type = env.ct->lub(then_type, else_type);
}
return this;
}

/* Recurisvely type checks the predicate and body, makes sure predicate is a Bool. */
Expression loop_class::type_check(type_env_t env) {
Symbol pred_type = pred->type_check(env)->type;
body->type_check(env);
if (pred_type != Bool) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "While condition did not evaluate to a boolean.\n";
type = Object;
} else {
type = Object;
}
return this;
}
/*

Type checks a linked list of branch/case expressions in the followin format:
case e0 of x1:T1=>e1, ..., xn:Tn=>en esac
For each branch i, the current identifier xi is saved in a new scope and the
expression ei is evaluated. The typcase class evaluates the the least upper
bound of the evaluated types.
*/
Expression typcase_class::type_check(type_env_t env) {
expr->type_check(env)->type;// O(N^2) check to make sure there are no duplicate types.
int case_idx_outer = cases->first();
while (cases->more(case_idx_outer)) {
int case_idx_inner = cases->first();
while (cases->more(case_idx_inner)) {
if (case_idx_outer != case_idx_inner && cases->nth(case_idx_outer)->get_type() == cases->nth(case_idx_inner)->get_type()) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Duplicate branch " << cases->nth(case_idx_outer)->get_type()
<< " in case statement.\n";
type = Object;
return this;
}
case_idx_inner = cases->next(case_idx_inner);
}
case_idx_outer = cases->next(case_idx_outer);
}int case_idx = cases->first();
Symbol case_type = cases->nth(case_idx)->type_check(env);
case_idx = cases->next(case_idx);
while (cases->more(case_idx)) {
env.om->enterscope();
Symbol branch_type = cases->nth(case_idx)->type_check(env);
case_type = env.ct->lub(case_type, branch_type);
env.om->exitscope();
case_idx = cases->next(case_idx);
}
type = case_type;
return this;
}

/* Type checks each enclosing expression. Imposes no type conditions. */
Expression block_class::type_check(type_env_t env) {
Symbol last_type = Object;
int body_idx = body->first();
while (body->more(body_idx)) {
last_type = body->nth(body_idx)->type_check(env)->type;
body_idx = body->next(body_idx);
}
type = last_type;
return this;
}
/*

Given the expression: let x:T0[<-e1] in e2:T2,

Evaluates the initializing expression e0 if provided.


If e0 is provided, makes sure the evaluated type T1 is a child of the

declared type T0.

Enters a new environment scope with the identifier x bound to the declared

type T0.

Typechecks the body e2, and the type evaluates to the evaluated type T2.
*/
Expression let_class::type_check(type_env_t env) {
Symbol decl_type = type_decl;
Symbol init_type = init->type_check(env)->type;
if (identifier == self) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "'self' cannot be bound in a 'let' expression.\n";
type = Object;
} else if (init_type == No_type) {
env.om->enterscope();
env.om->addid(identifier, &decl_type);
type = body->type_check(env)->type;
env.om->exitscope();
} else if (!env.ct->is_child(init_type, decl_type)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Expression must evaluate to a child of " << decl_type << ".\n";
type = Object;
} else {
env.om->enterscope();
env.om->addid(identifier, &decl_type);
type = body->type_check(env)->type;
env.om->exitscope();
}
return this;
}


/*

The following arithmetic classes are self-explanatory:
+, -, *, /, ~, <, =, !
*/
Expression plus_class::type_check(type_env_t env) {
Symbol left_type = e1->type_check(env)->type;
Symbol right_type = e2->type_check(env)->type;
if (left_type != Int || right_type != Int) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "non-Int arguments " << left_type << " + " << right_type << ".\n";
type = Object;
} else {
type = Int;
}
return this;
}

Expression sub_class::type_check(type_env_t env) {
Symbol left_type = e1->type_check(env)->type;
Symbol right_type = e2->type_check(env)->type;
if (left_type != Int || right_type != Int) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "non-Int arguments " << left_type << " - " << right_type << ".\n";
type = Object;
} else {
type = Int;
}
return this;
}
Expression mul_class::type_check(type_env_t env) {
Symbol left_type = e1->type_check(env)->type;
Symbol right_type = e2->type_check(env)->type;
if (left_type != Int || right_type != Int) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "non-Int arguments " << left_type << " * " << right_type << ".\n";
type = Object;
} else {
type = Int;
}
return this;
}
Expression divide_class::type_check(type_env_t env) {
Symbol left_type = e1->type_check(env)->type;
Symbol right_type = e2->type_check(env)->type;
if (left_type != Int || right_type != Int) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "non-Int arguments " << left_type << " / " << right_type << ".\n";
type = Object;
} else {
type = Int;
}
return this;
}
Expression neg_class::type_check(type_env_t env) {
Symbol operand_type = e1->type_check(env)->type;
if (operand_type != Int) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "non-Int argument ~" << operand_type << ".\n";
type = Object;
} else {
type = Int;
}
return this;
}
Expression lt_class::type_check(type_env_t env) {
Symbol left_type = e1->type_check(env)->type;
Symbol right_type = e2->type_check(env)->type;
if (left_type != Int || right_type != Int) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "non-Int arguments " << left_type << " < " << right_type << ".\n";
type = Object;
} else {
type = Bool;
}
return this;
}
Expression eq_class::type_check(type_env_t env) {
Symbol left_type = e1->type_check(env)->type;
Symbol right_type = e2->type_check(env)->type;
bool invalid_comparison =
(left_type == Int && right_type != Int) || (left_type != Int && right_type == Int) ||
(left_type == Str && right_type != Str) || (left_type != Str && right_type == Str) ||
(left_type == Bool && right_type != Bool) || (left_type != Bool && right_type == Bool);
if (invalid_comparison) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Cannot compare arguments " << left_type << " = " << right_type << ".\n";
type = Object;
} else {
type = Bool;
}
return this;
}
Expression leq_class::type_check(type_env_t env) {
Symbol left_type = e1->type_check(env)->type;
Symbol right_type = e2->type_check(env)->type;
if (left_type != Int || right_type != Int) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "non-Int arguments " << left_type << " <= " << right_type << ".\n";
type = Object;
} else {
type = Bool;
}
return this;
}
Expression comp_class::type_check(type_env_t env) {
Symbol operand_type = e1->type_check(env)->type;
if (operand_type != Bool) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "non-Bool argument !" << operand_type << ".\n";
type = Object;
} else {
type = Bool;
}
return this;
}
/* Primitive constants */
Expression int_const_class::type_check(type_env_t env) {
type = Int;
return this;
}
Expression bool_const_class::type_check(type_env_t env) {
type = Bool;
return this;
}
Expression string_const_class::type_check(type_env_t env) {
type = Str;
return this;
}
Expression new__class::type_check(type_env_t env) {
if (type_name != SELF_TYPE && !env.ct->class_exists(type_name)) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "'new' used with undefined class " << type_name << ".\n";
type = Object;
} else {
type = type_name;
}
return this;
}
Expression isvoid_class::type_check(type_env_t env) {
e1->type_check(env);
type = Bool;
return this;
}
Expression no_expr_class::type_check(type_env_t env) {
type = No_type;
return this;
}
Expression object_class::type_check(type_env_t env) {
if (name == self) {
type = SELF_TYPE;
} else {
Symbol* looked_up = env.om->lookup(name);
if (looked_up == NULL) {
ostream& err_stream = env.ct->semant_error(env.curr->get_filename(), this);
err_stream << "Could not find identifier " << name << " in current scope.\n";
type = Object;
} else {
type = *looked_up;
}
}
return this;
}
