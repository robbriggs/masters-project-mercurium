/*--------------------------------------------------------------------
  (C) Copyright 2006-2013 Barcelona Supercomputing Center
                          Centro Nacional de Supercomputacion
  
  This file is part of Mercurium C/C++ source-to-source compiler.
  
  See AUTHORS file in the top level directory for information
  regarding developers and contributors.
  
  This library is free software; you can redistribute it and/or
  modify it under the terms of the GNU Lesser General Public
  License as published by the Free Software Foundation; either
  version 3 of the License, or (at your option) any later version.
  
  Mercurium C/C++ source-to-source compiler is distributed in the hope
  that it will be useful, but WITHOUT ANY WARRANTY; without even the
  implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
  PURPOSE.  See the GNU Lesser General Public License for more
  details.
  
  You should have received a copy of the GNU Lesser General Public
  License along with Mercurium C/C++ source-to-source compiler; if
  not, write to the Free Software Foundation, Inc., 675 Mass Ave,
  Cambridge, MA 02139, USA.
--------------------------------------------------------------------*/




#include <string.h>
#include <ctype.h>

#include "cxx-ast.h"
#include "cxx-prettyprint.h"
#include "cxx-scope.h"
#include "cxx-buildscope.h"
#include "cxx-gccsupport.h"
#include "cxx-utils.h"
#include "cxx-cexpr.h"
#include "cxx-typeutils.h"
#include "cxx-ambiguity.h"
#include "cxx-exprtype.h"
#include "cxx-tltype.h"
#include "cxx-entrylist.h"
#include "cxx-diagnostic.h"

/*
 * Very specific bits of gcc support should be in this file
 */

const char* list_of_gcc_type_attributes[] =
{
    "aligned",
    "deprecated",
    "may_alias",
    "packed",
    "transparent_union",
    "unused",

    NULL
};

char gcc_attribute_is_type_attribute(const char* identifier)
{
    char is_type_attribute = 0;
    int i = 0;
    while (!is_type_attribute
            && list_of_gcc_type_attributes[i] != NULL)
    {
        const char* attribute_name = list_of_gcc_type_attributes[i];
        const char* __attribute_name__ = strappend(strappend("__", attribute_name),"__");
        is_type_attribute =
            (strcmp(identifier, attribute_name) == 0)
            || (strcmp(identifier, __attribute_name__) == 0);
        ++i;
    }
    return is_type_attribute;
}

static char fix_gather_type_to_match_mode(gather_decl_spec_t* gather_info, 
        char floating,
        char is_complex,
        _size_t bytes)
{
    type_t* signed_0_integral_types[] =
    {
        get_char_type(), // This is the difference with the signed table below
        get_signed_short_int_type(),
        get_signed_int_type(),
        get_signed_long_int_type(),
        get_signed_long_long_int_type(),
#ifdef HAVE_INT128
        get_signed_int128_type(),
#endif
        NULL,
    };

    type_t* signed_integral_types[] =
    {
        get_signed_char_type(),
        get_signed_short_int_type(),
        get_signed_int_type(),
        get_signed_long_int_type(),
        get_signed_long_long_int_type(),
#ifdef HAVE_INT128
        get_signed_int128_type(),
#endif
        NULL,
    };

    type_t* unsigned_integral_types[] =
    {
        get_unsigned_char_type(),
        get_unsigned_short_int_type(),
        get_unsigned_int_type(),
        get_unsigned_long_int_type(),
        get_unsigned_long_long_int_type(),
#ifdef HAVE_INT128
        get_unsigned_int128_type(),
#endif
        NULL,
    };

    type_t* float_types[] =
    {
        get_float_type(),
        get_double_type(),
        get_long_double_type(),
#ifdef HAVE_QUADMATH_H
        get_float128_type(),
#endif
        NULL,
    };

    type_t** types = signed_0_integral_types;

    if (floating)
        types = float_types;
    else if (gather_info->is_unsigned)
        types = unsigned_integral_types;
    else if (gather_info->is_signed)
        types = signed_integral_types;

    char match_found = 0;
    type_t* match_type = NULL;

    int i = 0;
    while (types[i] != NULL
            && !match_found)
    {
        if (type_get_size(types[i]) == bytes)
        {
            match_found = 1;
            match_type = types[i];
        }
        i++;
    }

    if (match_found)
    {
        if (is_complex)
        {
            match_type = get_complex_type(match_type);
        }

        gather_info->is_overriden_type = 1;
        gather_info->mode_type = match_type;
    }

    return match_found;
}

void gather_one_gcc_attribute(const char* attribute_name,
        AST expression_list,
        gather_decl_spec_t* gather_info,
        decl_context_t decl_context)
{
    char do_not_keep_attribute = 0;

    nodecl_t nodecl_expression_list = nodecl_null();
    /*
     * Vector support
     */
    if (expression_list != NULL
            && (strcmp(attribute_name, "vector_size") == 0
                || strcmp(attribute_name, "__vector_size__") == 0))
    {
        do_not_keep_attribute = 1;
        if (ASTSon0(expression_list) != NULL)
        {
            running_error("%s: error: attribute 'vector_size' only allows one argument",
                    ast_location(expression_list));
        }

        // Evaluate the expression
        AST argument = ASTSon1(expression_list);
        nodecl_t nodecl_expr = nodecl_null();
        if (check_expression(argument, decl_context, &nodecl_expr))
        {
            if (nodecl_is_constant(nodecl_expr))
            {
                int vector_size = const_value_cast_to_4(nodecl_get_constant(nodecl_expr));

                gather_info->vector_size = vector_size;
                gather_info->is_vector = 1;

                nodecl_expression_list = nodecl_make_list_1(nodecl_expr);
            }
            else
            {
                fprintf(stderr, "%s: warning: ignoring attribute 'vector_size' since the expression is not constant\n",
                        ast_location(expression_list));
            }
        }
        else
        {
            fprintf(stderr, "%s: warning: ignoring attribute 'vector_size' since the expression is not valid\n",
                    ast_location(expression_list));
        }
    }
    else if (strcmp(attribute_name, "generic_vector") == 0)
    {
        do_not_keep_attribute = 1;
        if (expression_list != NULL)
        {
            running_error("%s: error: attribute 'generic_vector' does not allow arguments",
                    ast_location(expression_list));
        }

        gather_info->vector_size = 0;
        gather_info->is_vector = 1;
    }
    else if (strcmp(attribute_name, "spu_vector") == 0)
    {
        do_not_keep_attribute = 1;
        // Hardcoded to what a SPU can do
        gather_info->is_vector = 1;
        gather_info->vector_size = 16;
    }
    else if (expression_list != NULL
            && strcmp(attribute_name, "altivec") == 0)
    {
        do_not_keep_attribute = 1;
        AST argument = advance_expression_nest(ASTSon1(expression_list));
        if (ASTType(argument) == AST_SYMBOL)
        {
            const char *argument_text = ASTText(argument);
            if (strcmp(argument_text, "vector__") == 0)
            {
                // Hardcoded to what an Altivec unit can do
                // that (oh, miracle!) is the same as a SPU
                gather_info->is_vector = 1;
                gather_info->vector_size = 16;

                nodecl_expression_list = 
                    nodecl_make_list_1(nodecl_make_text("vector__", ast_get_locus(argument)));
            }
        }
    }
    else if (expression_list != NULL
            && (strcmp(attribute_name, "aligned") == 0
                || strcmp(attribute_name, "__aligned__") == 0))
    {
        // Normalize the name
        attribute_name = "aligned";

        if (ASTSon0(expression_list) != NULL)
        {
            error_printf("%s: error: attribute 'aligned' only allows one argument",
                    ast_location(expression_list));
            do_not_keep_attribute = 1;
        }
        else
        {
            // Evaluate the expression
            AST argument = ASTSon1(expression_list);
            check_expression(argument, decl_context, &nodecl_expression_list);
            if (nodecl_is_err_expr(nodecl_expression_list))
            {
                do_not_keep_attribute = 1;
            }
            else
            {
                if (!nodecl_expr_is_value_dependent(nodecl_expression_list)
                        && !nodecl_is_constant(nodecl_expression_list))
                {
                    error_printf("%s: error: attribute 'aligned' is not constant",
                            ast_location(expression_list));
                    do_not_keep_attribute = 1;
                }
                else
                {
                    nodecl_expression_list = nodecl_make_list_1(nodecl_expression_list);
                }
            }
        }
    }
    else if (expression_list != NULL
            && (strcmp(attribute_name, "mode") == 0
                || strcmp(attribute_name, "__mode__") == 0))
    {
        do_not_keep_attribute = 1;
        if (ASTSon0(expression_list) != NULL)
        {
            running_error("%s: error: attribute 'mode' only allows one argument",
                    ast_location(expression_list));
        }

        AST argument = advance_expression_nest(ASTSon1(expression_list));

        char ignored = 0;
        if (ASTType(argument) == AST_SYMBOL)
        {
            const char *size_mode = ASTText(argument);

            nodecl_expression_list = 
                nodecl_make_list_1(nodecl_make_text(size_mode, ast_get_locus(argument)));

            // FIXME - Can a vector mode start with two underscores ?
            if (size_mode[0] != 'V')
            {
                // Do nothing if we don't do sizeof
                if (!CURRENT_CONFIGURATION->disable_sizeof)
                {
                    /*
                       QI - An integer that is as wide as the smallest addressable unit, usually 8 bits.
                       HI - An integer, twice as wide as a QI mode integer, usually 16 bits.
                       SI - An integer, four times as wide as a QI mode integer, usually 32 bits.
                       DI - An integer, eight times as wide as a QI mode integer, usually 64 bits.
                       SF - A floating point value, as wide as a SI mode integer, usually 32 bits.
                       DF - A floating point value, as wide as a DI mode integer, usually 64 bits. 
                     */
                    struct 
                    {
                        const char* mode_name;
                        char floating;
                        char is_complex;
                        _size_t bytes;
                    } mode_list[] =
                    {
                        // Integral types
                        { "QI",     0, 0, 1 },
                        { "__QI__", 0, 0, 1 },
                        { "HI",     0, 0, 2 },
                        { "__HI__", 0, 0, 2 },
                        { "SI",     0, 0, 4 },
                        { "__SI__", 0, 0, 4 },
                        { "DI",     0, 0, 8 },
                        { "__DI__", 0, 0, 8 },
                        // Floating types
                        { "SF",     1, 0, 4 },
                        { "__SF__", 1, 0, 4 },
                        { "DF",     1, 0, 8 },
                        { "__DF__", 1, 0, 8 },
                        // Complex types (size is given for the base type of
                        // the complex)
                        { "TC",     1, 1, 16 },
                        { "__TC__", 1, 1, 16 },
                    };

                    char found = 0;

                    if (strcmp(size_mode, "__pointer__") == 0
                        || strcmp(size_mode, "pointer") == 0)
                    {
                        fix_gather_type_to_match_mode(gather_info,
                                /* floating */ 0, /* is_complex */ 0,
                                CURRENT_CONFIGURATION->type_environment->sizeof_pointer);
                        found = 1;
                    }
                    else if (strcmp(size_mode, "__word__") == 0
                            || strcmp(size_mode, "word") == 0)
                    {
                        // what is word mode??? At the moment use the size of a long
                        // since it matches what gcc does
                        fix_gather_type_to_match_mode(gather_info,
                                /* floating */ 0, /* is_complex */ 0,
                                CURRENT_CONFIGURATION->type_environment->sizeof_signed_long);
                        found = 1;
                    }
                    else if (strcmp(size_mode, "__byte__") == 0
                        || strcmp(size_mode, "byte") == 0)
                    {
                        fix_gather_type_to_match_mode(gather_info,
                                /* floating */ 0, /* is_complex */ 0,
                                /* 1 byte */ 1);
                        found = 1;
                    }

                    // Find in the table above if not found yet
                    int i;
                    int max_mode = STATIC_ARRAY_LENGTH(mode_list);
                    for (i = 0; i < max_mode && !found; i++)
                    {
                        if (strcmp(size_mode, mode_list[i].mode_name) == 0)
                        {
                            found = 1;
                            fix_gather_type_to_match_mode(gather_info, 
                                    mode_list[i].floating,
                                    mode_list[i].is_complex,
                                    mode_list[i].bytes);
                        }
                    }

                    if (!found)
                    {
                        ignored = 1;
                    }
                }
            }
            else
            {
                fprintf(stderr, "%s: warning: attribute 'mode' is deprecated better use 'vector_size'\n", 
                        ast_location(expression_list));

                // Skip first character
                char *number_of_elements_str = xstrdup(&size_mode[1]);
                char *p = number_of_elements_str;

                while (isdigit(*p))
                {
                    p++;
                }

                if (*p == '\0')
                {
                    ignored = 1;
                }
                else
                {
                    char size;
                    char nature;

                    size = *p;

                    // End the number_of_elements_str here
                    *p = '\0';

                    p++;


                    if ((*p == '\0') || 
                            (p == number_of_elements_str))
                    {
                        ignored = 1;
                    }
                    else
                    {
                        nature = *p;
                        p++;

                        int num_elements = atoi(number_of_elements_str);

                        /*
                           From gcc documentation: 

                           QI - An integer that is as wide as the smallest addressable unit, usually 8 bits.
                           HI - An integer, twice as wide as a QI mode integer, usually 16 bits.
                           SI - An integer, four times as wide as a QI mode integer, usually 32 bits.
                           DI - An integer, eight times as wide as a QI mode integer, usually 64 bits.
                           SF - A floating point value, as wide as a SI mode integer, usually 32 bits.
                           DF - A floating point value, as wide as a DI mode integer, usually 64 bits. 
                         */
                        if (*p != '\0')
                        {
                            ignored = 1;
                        }
                        else
                        {
                            if (nature == 'I')
                            {
                                if (size == 'Q')
                                {
                                    gather_info->mode_type = get_signed_char_type();
                                }
                                else if (size == 'H')
                                {
                                    gather_info->mode_type = get_signed_short_int_type();
                                }
                                else if (size == 'S')
                                {
                                    gather_info->mode_type = get_signed_int_type();
                                }
                                else if (size == 'D')
                                {
                                    gather_info->mode_type = get_signed_long_long_int_type();
                                }
                                else
                                {
                                    ignored = 1;
                                }
                            }
                            else if (nature == 'F')
                            {
                                if (size == 'S')
                                {
                                    gather_info->mode_type = get_float_type();
                                }
                                else if (size == 'D')
                                {
                                    gather_info->mode_type = get_double_type();
                                }
                                else
                                {
                                    ignored = 1;
                                }
                            }
                            else
                            {
                                ignored = 1;
                            }

                            if (!ignored)
                            {
                                gather_info->vector_size = num_elements
                                    * get_sizeof_type(gather_info->mode_type);
                                gather_info->is_vector = 1;
                            }
                        }
                    }
                }

                xfree(number_of_elements_str);
            }
        }
        else
        {
            ignored = 1;
        }

        if (ignored)
        {
            fprintf(stderr, "%s: warning: ignoring attribute 'mode'\n",
                    ast_location(expression_list));
        }
    }
    else if (strcmp(attribute_name, "__strong__") == 0)
    {
        gather_info->is_inline = 1;
    }
    else if (strcmp(attribute_name, "used") == 0)
    {
        gather_info->emit_always = 1;
    }
    else if (strcmp(attribute_name, "__transparent_union__") == 0 || strcmp(attribute_name, "transparent_union") == 0)
    {
        gather_info->is_transparent_union = 1;
    }
    // CUDA attributes
    else if (CURRENT_CONFIGURATION->enable_cuda && strcmp(attribute_name, "global") == 0)
    {
        gather_info->cuda.is_global = 1;
    }
    else if (CURRENT_CONFIGURATION->enable_cuda && strcmp(attribute_name, "device") == 0)
    {
        gather_info->cuda.is_device = 1;
    }
    else if (CURRENT_CONFIGURATION->enable_cuda && strcmp(attribute_name, "host") == 0)
    {
        gather_info->cuda.is_host = 1;
    }
    else if (CURRENT_CONFIGURATION->enable_cuda && strcmp(attribute_name, "shared") == 0)
    {
        gather_info->cuda.is_shared = 1;
    }
    else if (CURRENT_CONFIGURATION->enable_cuda && strcmp(attribute_name, "constant") == 0)
    {
        gather_info->cuda.is_constant = 1;
    }
    else
    {
        // Unknown attribute, keep its arguments as a literal list
        if (expression_list != NULL)
        {
            AST it;
            for_each_element(expression_list, it)
            {
                AST expr = ASTSon1(it);

                nodecl_expression_list = nodecl_append_to_list(nodecl_expression_list,
                        nodecl_make_text(prettyprint_in_buffer(expr), ast_get_locus(expr)));
            }
        }
    }

    // Save it in the gather_info structure
    if (!do_not_keep_attribute)
    {
        if (gather_info->num_gcc_attributes == MCXX_MAX_GCC_ATTRIBUTES_PER_SYMBOL)
        {
            running_error("Too many gcc attributes, maximum supported is %d\n", MCXX_MAX_GCC_ATTRIBUTES_PER_SYMBOL);
        }

        gcc_attribute_t current_gcc_attribute;

        current_gcc_attribute.attribute_name = uniquestr(attribute_name);
        current_gcc_attribute.expression_list = nodecl_expression_list;

        P_LIST_ADD(gather_info->gcc_attributes, gather_info->num_gcc_attributes, current_gcc_attribute);
    }
}

void gather_gcc_attribute(AST attribute,
        gather_decl_spec_t* gather_info,
        decl_context_t decl_context)
{
    ERROR_CONDITION(ASTType(attribute) != AST_GCC_ATTRIBUTE,
            "Invalid node", 0);
    AST iter;
    AST list = ASTSon0(attribute);

    if (list != NULL)
    {
        for_each_element(list, iter)
        {
            AST gcc_attribute_expr = ASTSon1(iter);

            AST identif = ASTSon0(gcc_attribute_expr);
            AST expression_list = ASTSon1(gcc_attribute_expr);

            const char *attribute_name = ASTText(identif);

            if (attribute_name == NULL)
                continue;

            gather_one_gcc_attribute(attribute_name, expression_list, gather_info, decl_context);
        }
    }
}

void keep_gcc_attributes_in_symbol(
        scope_entry_t* entry,
        gather_decl_spec_t* gather_info)
{
    // Combine them
    int i;
    for (i = 0; i < gather_info->num_gcc_attributes; i++)
    {
        char found = 0;
        int j;
        for (j = 0; j < entry->entity_specs.num_gcc_attributes && !found; j++)
        {
            found = (strcmp(entry->entity_specs.gcc_attributes[j].attribute_name,
                        gather_info->gcc_attributes[i].attribute_name) == 0);
        }

        if (found)
        {
            // Update with the freshest value 
            entry->entity_specs.gcc_attributes[j-1].expression_list = gather_info->gcc_attributes[i].expression_list;
        }
        else
        {
            entry->entity_specs.num_gcc_attributes++;
            entry->entity_specs.gcc_attributes = xrealloc(entry->entity_specs.gcc_attributes,
                    sizeof(*entry->entity_specs.gcc_attributes) * entry->entity_specs.num_gcc_attributes);
            entry->entity_specs.gcc_attributes[entry->entity_specs.num_gcc_attributes - 1] = gather_info->gcc_attributes[i];
        }
    }
}


void apply_gcc_attribute_to_type(AST a,
        type_t** type,
        decl_context_t decl_context UNUSED_PARAMETER)
{
    ERROR_CONDITION(ASTType(a) != AST_GCC_ATTRIBUTE, "Invalid node", 0);

    AST gcc_attribute_list = ASTSon0(a);
    AST it;

    for_each_element(gcc_attribute_list, it)
    {
        AST gcc_attribute_expr = ASTSon1(it);

        AST identif = ASTSon0(gcc_attribute_expr);
        AST expr_list = ASTSon1(gcc_attribute_expr);
        const char *attribute_name = ASTText(identif);

        if (attribute_name == NULL)
            return;

        gcc_attribute_t gcc_attr;
        gcc_attr.attribute_name = attribute_name;
        gcc_attr.expression_list = nodecl_null();

        // Normalize this name as the FE uses it elsewhere
        if (expr_list != NULL
                && (strcmp(attribute_name, "aligned") == 0
                    || strcmp(attribute_name, "__aligned__") == 0))
        {
            attribute_name = "aligned";

            if (ASTSon0(expr_list) != NULL)
            {
                error_printf("%s: error: attribute 'aligned' only allows one argument",
                        ast_location(expr_list));
            }

            AST expr = ASTSon1(expr_list);

            nodecl_t nodecl_expr = nodecl_null();
            check_expression(expr, decl_context, &nodecl_expr);

            if (nodecl_is_err_expr(nodecl_expr))
                continue;

            if (!nodecl_expr_is_value_dependent(nodecl_expr)
                    && !nodecl_is_constant(nodecl_expr))
            {
                error_printf("%s: error: attribute 'aligned' is not constant",
                        ast_location(expr_list));
            }

            gcc_attr.expression_list = nodecl_make_list_1(nodecl_expr);
        }
        else
        {
            if (expr_list != NULL)
            {
                AST it2;
                for_each_element(expr_list, it2)
                {
                    AST expr = ASTSon1(it2);

                    gcc_attr.expression_list = nodecl_append_to_list(gcc_attr.expression_list,
                            nodecl_make_text(prettyprint_in_buffer(expr), ast_get_locus(expr)));
                }
            }
        }

        *type = get_variant_type_add_gcc_attribute(*type, gcc_attr);
    }
}

/*
 * Type traits of g++
 */

static char eval_type_trait__has_nothrow_assign(type_t*, type_t*, decl_context_t);
static char eval_type_trait__has_nothrow_constructor(type_t*, type_t*, decl_context_t);
static char eval_type_trait__has_nothrow_copy(type_t*, type_t*, decl_context_t);
static char eval_type_trait__has_trivial_assign(type_t*, type_t*, decl_context_t);
static char eval_type_trait__has_trivial_constructor(type_t*, type_t*, decl_context_t);
static char eval_type_trait__has_trivial_copy(type_t*, type_t*, decl_context_t);
static char eval_type_trait__has_trivial_destructor(type_t*, type_t*, decl_context_t);
static char eval_type_trait__has_virtual_destructor(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_abstract(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_base_of(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_class(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_convertible_to(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_empty(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_enum(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_literal_type(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_pod(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_polymorphic(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_standard_layout(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_trivial(type_t*, type_t*, decl_context_t);
static char eval_type_trait__is_union(type_t*, type_t*, decl_context_t);

/*
   __has_nothrow_assign (type)

   If type is const qualified or is a reference type then the trait is false.
   Otherwise if __has_trivial_assign (type) is true then the trait is true,
   else if type is a cv class or union type with copy assignment operators
   that are known not to throw an exception then the trait is true, else it is
   false. Requires: type shall be a complete type, an array type of unknown
   bound, or is a void type. 

    */
static char eval_type_trait__has_nothrow_assign(type_t* first_type, type_t* second_type, decl_context_t decl_context)
{
    if (is_const_qualified_type(first_type)
            || is_lvalue_reference_type(first_type)
            || is_rvalue_reference_type(first_type))
        return 0;

    if (eval_type_trait__has_trivial_assign(first_type, second_type, decl_context))
        return 1;

    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);

        scope_entry_list_t* copy_assignment_operators = class_type_get_copy_assignment_operators(class_type);
        scope_entry_list_iterator_t* it = NULL;

        char result = 1;
        for (it = entry_list_iterator_begin(copy_assignment_operators);
                !entry_list_iterator_end(it) && result;
                entry_list_iterator_next(it))
        {
            scope_entry_t* entry = entry_list_iterator_current(it);
            if (entry->entity_specs.any_exception
                    || entry->entity_specs.num_exceptions != 0)
            {
                result = 0;
            }
        }

        entry_list_iterator_free(it);
        entry_list_free(copy_assignment_operators);

        return result;
    }

    return 0;
}

/*
   __has_nothrow_constructor (type)

   If __has_trivial_constructor (type) is true then the trait is true, else if
   type is a cv class or union type (or array thereof) with a default
   constructor that is known not to throw an exception then the trait is true,
   else it is false. Requires: type shall be a complete type, an array type of
   unknown bound, or is a void type. 

*/
static char eval_type_trait__has_nothrow_constructor(type_t* first_type, type_t* second_type, decl_context_t decl_context)
{
    if (eval_type_trait__has_trivial_constructor(first_type, second_type, decl_context))
        return 1;

    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);

        scope_entry_t* default_constructor  = class_type_get_default_constructor(class_type);
        if (default_constructor == NULL)
        {
            return 0;
        }

        if (default_constructor->entity_specs.any_exception
                || default_constructor->entity_specs.num_exceptions != 0)
            return 0;

        return 1;
    }

    return 0;
}

/*
   __has_nothrow_copy (type)

   If __has_trivial_copy (type) is true then the trait is true, else if type
   is a cv class or union type with copy constructors that are known not to
   throw an exception then the trait is true, else it is false. Requires: type
   shall be a complete type, an array type of unknown bound, or is a void
   type. 

*/
static char eval_type_trait__has_nothrow_copy(type_t* first_type, type_t* second_type, decl_context_t decl_context)
{
    if (eval_type_trait__has_trivial_copy(first_type, second_type, decl_context))
        return 1;

    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);

        scope_entry_list_t* constructors = class_type_get_copy_constructors(class_type);
        scope_entry_list_iterator_t* it = NULL;
        char result = 1;
        for (it = entry_list_iterator_begin(constructors);
                !entry_list_iterator_end(it) && result;
                entry_list_iterator_next(it))
        {
            scope_entry_t* entry = entry_list_iterator_current(it);

            if (entry->entity_specs.any_exception
                    || entry->entity_specs.num_exceptions != 0)
                result = 0;
        }

        entry_list_iterator_free(it);
        entry_list_free(constructors);

        return result;
    }

    return 0;
}

/*
   __has_trivial_assign (type)

   If type is const qualified or is a reference type then the trait is false.
   Otherwise if __is_pod (type) is true then the trait is true, else if type is a
   cv class or union type with a trivial copy assignment ([class.copy]) then the
   trait is true, else it is false. Requires: type shall be a complete type, an
   array type of unknown bound, or is a void type. 

*/
static char eval_type_trait__has_trivial_assign(type_t* first_type, type_t* second_type, decl_context_t decl_context)
{
    if (is_const_qualified_type(first_type)
            || is_lvalue_reference_type(first_type)
            || is_rvalue_reference_type(first_type))
        return 0;

    if (eval_type_trait__is_pod(first_type, second_type, decl_context))
        return 1;

    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);

        scope_entry_list_t* copy_assignment_operators = class_type_get_copy_assignment_operators(class_type);
        scope_entry_list_iterator_t* it = NULL;

        char result = 1;
        for (it = entry_list_iterator_begin(copy_assignment_operators);
                !entry_list_iterator_end(it) && result;
                entry_list_iterator_next(it))
        {
            scope_entry_t* entry = entry_list_iterator_current(it);
            if (!entry->entity_specs.is_trivial)
                result = 0;
        }

        entry_list_iterator_free(it);
        entry_list_free(copy_assignment_operators);

        return result;
    }

    return 0;
}

/*
   __has_trivial_constructor (type)

    If __is_pod (type) is true then the trait is true, else if type is a cv
    class or union type (or array thereof) with a trivial default constructor
    ([class.ctor]) then the trait is true, else it is false. Requires: type
    shall be a complete type, an array type of unknown bound, or is a void
    type. 
*/
static char eval_type_trait__has_trivial_constructor(type_t* first_type, type_t* second_type, decl_context_t decl_context)
{
    if (eval_type_trait__is_pod(first_type, second_type, decl_context))
        return 1;

    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);

        scope_entry_t* default_constructor = class_type_get_default_constructor(class_type);

        if (default_constructor == NULL)
            return 0;

        return default_constructor->entity_specs.is_trivial;
    }

    return 0;
}

/*
   __has_trivial_copy (type)

   If __is_pod (type) is true or type is a reference type then the trait is
   true, else if type is a cv class or union type with a trivial copy
   constructor ([class.copy]) then the trait is true, else it is false.
   Requires: type shall be a complete type, an array type of unknown bound, or is
   a void type. 

*/
static char eval_type_trait__has_trivial_copy(type_t* first_type, type_t* second_type, decl_context_t decl_context)
{
    if (eval_type_trait__is_pod(first_type, second_type, decl_context)
            || is_rvalue_reference_type(first_type)
            || is_lvalue_reference_type(first_type))
        return 1;

    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);

        scope_entry_list_t* constructors = class_type_get_copy_constructors(class_type);
        scope_entry_list_iterator_t* it = NULL;
        char result = 1;
        for (it = entry_list_iterator_begin(constructors);
                !entry_list_iterator_end(it) && result;
                entry_list_iterator_next(it))
        {
            scope_entry_t* entry = entry_list_iterator_current(it);
            if (!entry->entity_specs.is_trivial)
                result = 0;
        }

        entry_list_iterator_free(it);
        entry_list_free(constructors);

        return result;
    }

    return 0;
}
/*
   __has_trivial_destructor (type)

   If __is_pod (type) is true or type is a reference type then the trait is
   true, else if type is a cv class or union type (or array thereof) with a
   trivial destructor ([class.dtor]) then the trait is true, else it is false.
   Requires: type shall be a complete type, an array type of unknown bound, or is
   a void type. 

*/

static char eval_type_trait__has_trivial_destructor(type_t* first_type, type_t* second_type, decl_context_t decl_context)
{
    if (eval_type_trait__is_pod(first_type, second_type, decl_context))
        return 1;

    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);

        scope_entry_t* destructor = class_type_get_destructor(class_type);

        return destructor->entity_specs.is_trivial;
    }

    return 0;
}

/*
    __has_virtual_destructor (type)

    If type is a class type with a virtual destructor ([class.dtor]) then the
    trait is true, else it is false. Requires: type shall be a complete type,
    an array type of unknown bound, or is a void type. 
*/
static char eval_type_trait__has_virtual_destructor(type_t* first_type, type_t* second_type UNUSED_PARAMETER, decl_context_t decl_context UNUSED_PARAMETER)
{
    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);

        scope_entry_t* destructor = class_type_get_destructor(class_type);

        return destructor->entity_specs.is_virtual;
    }

    return 0;
}

/*
    __is_abstract (type)

    If type is an abstract class ([class.abstract]) then the trait is true,
    else it is false. Requires: type shall be a complete type, an array type of
    unknown bound, or is a void type. 
*/
static char eval_type_trait__is_abstract(type_t* first_type UNUSED_PARAMETER, 
        type_t* second_type UNUSED_PARAMETER, 
        decl_context_t decl_context UNUSED_PARAMETER)
{
    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);
        return class_type_is_abstract(class_type);
    }

    return 0;
}

/*
   __is_base_of (base_type, derived_type)

   If base_type is a base class of derived_type ([class.derived]) then the
   trait is true, otherwise it is false. Top-level cv qualifications of
   base_type and derived_type are ignored. For the purposes of this trait, a
   class type is considered is own base. Requires: if __is_class (base_type)
   and __is_class (derived_type) are true and base_type and derived_type are
   not the same type (disregarding cv-qualifiers), derived_type shall be a
   complete type. Diagnostic is produced if this requirement is not met. 
*/

static char eval_type_trait__is_base_of(type_t* base_type, type_t* derived_type, decl_context_t decl_context UNUSED_PARAMETER)
{
    if (is_class_type(base_type)
            && is_class_type(derived_type))
    {
        type_t* base_class_type = get_actual_class_type(base_type);
        type_t* derived_class_type = get_actual_class_type(derived_type);

        return class_type_is_base(base_class_type, derived_class_type);
    }
    return 0;
}

/*
   __is_class (type)

   If type is a cv class type, and not a union type ([basic.compound]) the the trait is true, else it is false. 
*/
static char eval_type_trait__is_class(type_t* first_type, type_t* second_type UNUSED_PARAMETER, 
        decl_context_t decl_context UNUSED_PARAMETER)
{
    return is_class_type(first_type)
        && !is_union_type(first_type);
    return 0;
}

/*
 * UNDOCUMENTED !!!
 */
static char eval_type_trait__is_convertible_to(type_t* first_type UNUSED_PARAMETER, 
        type_t* second_type UNUSED_PARAMETER, 
        decl_context_t decl_context UNUSED_PARAMETER)
{
    WARNING_MESSAGE("Undocumented type trait '__is_convertible' used", 0);
    return 0;
}

/*
   __is_empty (type)

   If __is_class (type) is false then the trait is false. Otherwise type is
   considered empty if and only if: type has no non-static data members, or
   all non-static data members, if any, are bit-fields of length 0, and type
   has no virtual members, and type has no virtual base classes, and type has
   no base classes base_type for which __is_empty (base_type) is false.
   Requires: type shall be a complete type, an array type of unknown bound, or is
   a void type. 
*/
static char eval_type_trait__is_empty(type_t* first_type, 
        type_t* second_type UNUSED_PARAMETER, 
        decl_context_t decl_context)
{
    if (!eval_type_trait__is_class(first_type, NULL, decl_context))
        return 0;

    if (is_class_type(first_type))
        return class_type_is_empty(first_type);

    return 0;
}

/*
   __is_enum (type)

   If type is a cv enumeration type ([basic.compound]) the the trait is true,
   else it is false. 
*/
static char eval_type_trait__is_enum(type_t* first_type, type_t* second_type UNUSED_PARAMETER, decl_context_t decl_context UNUSED_PARAMETER)
{
    return (is_enum_type(first_type));
}

/*
     __is_literal_type (type)

    If type is a literal type ([basic.types]) the trait is true, else it is false.
    Requires: type shall be a complete type, (possibly cv-qualified) void, or an array of unknown bound. 
*/
static char eval_type_trait__is_literal_type(type_t* first_type, type_t* second_type UNUSED_PARAMETER, decl_context_t decl_context UNUSED_PARAMETER)
{
    return (is_literal_type(first_type));
}

/*
   __is_pod (type)

   If type is a cv POD type ([basic.types]) then the trait is true, else it is
   false. Requires: type shall be a complete type, an array type of unknown
   bound, or is a void type. 
*/
static char eval_type_trait__is_pod(type_t* first_type, 
        type_t* second_type UNUSED_PARAMETER, 
        decl_context_t decl_context UNUSED_PARAMETER)
{
    return is_pod_type(first_type);
}

/*
   __is_polymorphic (type)

   If type is a polymorphic class ([class.virtual]) then the trait is true,
   else it is false. Requires: type shall be a complete type, an array type of
   unknown bound, or is a void type

*/
static char eval_type_trait__is_polymorphic(type_t* first_type, 
        type_t* second_type UNUSED_PARAMETER, 
        decl_context_t decl_context UNUSED_PARAMETER)
{
    if (is_class_type(first_type))
    {
        type_t* class_type = get_actual_class_type(first_type);
        scope_entry_list_t* virtual_functions = class_type_get_virtual_functions(class_type);
        char there_are_virtual_functions = (virtual_functions != NULL);
        entry_list_free(virtual_functions);

        return there_are_virtual_functions;
    }

    return 0;
}

/*
    __is_standard_layout (type)

    If type is a standard-layout type ([basic.types]) the trait is true, else it is false.
    Requires: type shall be a complete type, (possibly cv-qualified) void,
    or an array of unknown bound.

*/
static char eval_type_trait__is_standard_layout(type_t* first_type,
        type_t* second_type UNUSED_PARAMETER,
        decl_context_t decl_context UNUSED_PARAMETER)
{
    return is_standard_layout_type(first_type);
}

/*
    __is_trivial (type)

    if type is a trivial type ([basic.types]) the trait is true, else it is false.
    Requires: type shall be a complete type, (possibly cv-qualified) void, or an
    array of unknown bound

*/
static char eval_type_trait__is_trivial(type_t* first_type,
        type_t* second_type UNUSED_PARAMETER,
        decl_context_t decl_context UNUSED_PARAMETER)
{
    return is_trivial_type(first_type);
}

/*
   __is_union (type)

   If type is a cv union type ([basic.compound]) then the trait is true, else it is false. 
*/
static char eval_type_trait__is_union(type_t* first_type, 
        type_t* second_type UNUSED_PARAMETER, 
        decl_context_t decl_context UNUSED_PARAMETER)
{
    return is_union_type(first_type);
}

typedef
struct gxx_type_traits_fun_type_tag
{
    const char* trait_name;

    char (*trait_calculus)(type_t* first_type, type_t* second_type, decl_context_t decl_context);
} gxx_type_traits_fun_type_t;

gxx_type_traits_fun_type_t type_traits_fun_list[] =
{
    { "__has_nothrow_assign", eval_type_trait__has_nothrow_assign },
    { "__has_nothrow_constructor", eval_type_trait__has_nothrow_constructor },
    { "__has_nothrow_copy", eval_type_trait__has_nothrow_copy },
    { "__has_trivial_assign", eval_type_trait__has_trivial_assign },
    { "__has_trivial_constructor", eval_type_trait__has_trivial_constructor },
    { "__has_trivial_copy", eval_type_trait__has_trivial_copy },
    { "__has_trivial_destructor", eval_type_trait__has_trivial_destructor },
    { "__has_virtual_destructor", eval_type_trait__has_virtual_destructor },
    { "__is_abstract", eval_type_trait__is_abstract },
    { "__is_base_of", eval_type_trait__is_base_of },
    { "__is_class", eval_type_trait__is_class },
    { "__is_convertible_to", eval_type_trait__is_convertible_to },
    { "__is_empty", eval_type_trait__is_empty },
    { "__is_enum", eval_type_trait__is_enum },
    { "__is_literal_type", eval_type_trait__is_literal_type },
    { "__is_pod", eval_type_trait__is_pod },
    { "__is_polymorphic", eval_type_trait__is_polymorphic },
    { "__is_standard_layout", eval_type_trait__is_standard_layout },
    { "__is_trivial", eval_type_trait__is_trivial },
    { "__is_union", eval_type_trait__is_union },
    // Sentinel
    {NULL, NULL},
};

// This function is used in this file and also in cxx-exprtype.c
void common_check_gxx_type_traits(type_t* lhs_type,
        type_t* rhs_type,
        type_t* gxx_trait_type,
        const char* trait_name,
        decl_context_t decl_context,
        const locus_t* locus,
        nodecl_t* nodecl_output)
{
    if (is_dependent_type(lhs_type)
            || (rhs_type != NULL
                && is_dependent_type(rhs_type)))
    {
        nodecl_t nodecl_lhs_type = nodecl_make_type(lhs_type, locus);
        nodecl_t nodecl_rhs_type_opt =
            (rhs_type == NULL) ?
            nodecl_null() : nodecl_make_type(lhs_type, locus);

        *nodecl_output = nodecl_make_gxx_trait(
                nodecl_lhs_type,
                nodecl_rhs_type_opt,
                gxx_trait_type,
                trait_name,
                locus);

        // This is like a constant expression with a dependent value
        nodecl_expr_set_is_value_dependent(*nodecl_output, 1);
        return;
    }

    int i = 0;
    char found = 0;
    while (type_traits_fun_list[i].trait_name != NULL
            && !found)
    {
        found = (strcmp(type_traits_fun_list[i].trait_name, trait_name) == 0);
        i++;
    }

    if (!found)
    {
        internal_error("Unknown trait '%s' at '%s:%d'\n", trait_name, locus);
    }

    // We are one ahead
    i--;

    if (type_traits_fun_list[i].trait_calculus == NULL)
    {
        internal_error("Unimplemented trait '%s' at '%s:%d'\n", trait_name, locus);
    }
    else
    {
        type_t* t = get_bool_type();

        const_value_t* val = NULL;

        if ((type_traits_fun_list[i].trait_calculus)(lhs_type, rhs_type, decl_context))
        {
            // true
            val = const_value_get_one(type_get_size(t), 0);
        }
        else
        {
            // false
            val = const_value_get_zero(type_get_size(t), 0);
        }
        *nodecl_output = nodecl_make_boolean_literal(t, val, locus);
    }
}

void check_gxx_type_traits(AST expression, decl_context_t decl_context, nodecl_t* nodecl_output)
{
    AST first_type_id = ASTSon0(expression);
    type_t* first_type = NULL;

    first_type = compute_type_for_type_id_tree(first_type_id, decl_context,
            /* out_simple_type */ NULL, /* out_gather_info */ NULL);
    if (is_error_type(first_type))
    {
        *nodecl_output = nodecl_make_err_expr(ast_get_locus(expression));
        return;
    }

    AST second_type_id = ASTSon1(expression);
    type_t* second_type = NULL;

    if (second_type_id != NULL)
    {
        second_type = compute_type_for_type_id_tree(second_type_id, decl_context,
                /* out_simple_type */ NULL, /* out_gather_info */ NULL);

        if (is_error_type(second_type))
        {
            *nodecl_output = nodecl_make_err_expr(ast_get_locus(expression));
            return;
        }
    }

    const char* trait_name = ASTText(expression);
    common_check_gxx_type_traits(first_type,
            second_type,
            get_bool_type(),
            trait_name,
            decl_context,
            ast_get_locus(expression),
            nodecl_output);
}
