#ifndef CXX_TYPEUTILS_H
#define CXX_TYPEUTILS_H

#include "cxx-ast.h"
#include "cxx-scope.h"

enum cv_equivalence_t
{
	CVE_UNKNOWN = 0,
	CVE_IGNORE,
	CVE_CONSIDER
};

char equivalent_types(type_t* t1, type_t* t2, scope_t* st, enum cv_equivalence_t cv_equiv);
char overloaded_function(function_info_t* f1, function_info_t* f2, scope_t* st, enum cv_equivalence_t cv_equiv);

/* Copy functions */
class_info_t* copy_class_info(class_info_t* class_info);
simple_type_t* copy_simple_type(simple_type_t* type_info);
type_t* copy_type(type_t* type);
function_info_t* copy_function_info(function_info_t* function_info);
array_info_t* copy_array_info(array_info_t* array_info);
pointer_info_t* copy_pointer_info(pointer_info_t* pointer_info);
enum_info_t* copy_enum_info(enum_info_t* enum_info);

// Equality functions
char equivalent_builtin_type(simple_type_t *t1, simple_type_t *t2, enum cv_equivalence_t cv_equiv);

// Conversion functions
type_t* simple_type_to_type(simple_type_t* simple_type_info);
char equivalent_simple_types(simple_type_t *t1, simple_type_t *t2, scope_t* st, enum cv_equivalence_t cv_equiv);

// Query functions
const char* get_builtin_type_name(simple_type_t* simple_type_info, scope_t* st);
type_t* base_type(type_t* t);

// Debug purpose functions
void print_declarator(type_t* printed_declarator, scope_t* st);

// Query functions
char is_fundamental_type(type_t* t);
char is_integral_type(type_t* t);
char is_floating_type(type_t* t);
char is_enumerated_type(type_t* t);

char can_be_promoted_to_dest(type_t* orig, type_t* dest);
char can_be_converted_to_dest(type_t* orig, type_t* dest);

char is_reference_type(type_t* t1);
char is_reference_related(type_t* rt1, type_t* rt2, scope_t* st);
char is_reference_compatible(type_t* t1, type_t* t2, scope_t* st);

char pointer_can_be_converted_to_dest(type_t* orig, type_t* dest, scope_t* st);

char* get_type_spec_name(AST type_spec, scope_t* st);
char* get_conversion_function_name(AST conversion_function_id, scope_t* st, type_t** result_conversion_type);

char is_class_type(type_t* possible_class);
char is_unnamed_class_type(type_t* possible_class);
char is_named_class_type(type_t* possible_class);
char is_base_class_of(type_t* possible_base, type_t* possible_derived);
type_t* get_class_type(type_t* class_type);

cv_qualifier_t get_cv_qualifier(type_t* type_info);

#endif // CXX_TYPEUTILS_H
