#include "hlt-extension.hpp"

using namespace TL::HLT;

FunctionExtension::FunctionExtension(FunctionDefinition funct_def, Expression extension_amount)
    : _funct_def(funct_def), _extension_amount(extension_amount), _function_symbol(_funct_def.get_function_symbol())
{
}

TL::Source FunctionExtension::get_source()
{
    do_extension();
    return _extension_code;
}

void FunctionExtension::do_extension()
{
    Source return_type, function_name, extended_args, extended_body;

    _extension_code
        << return_type << " " << function_name << "(" << extended_args << ")"
        << extended_body
        ;

    Type function_type = _function_symbol.get_type();
    if (!function_type.returns().is_void())
    {
        _ostream << _funct_def.get_ast().get_locus() << ": warning: function should return void" << std::endl;
    }
    // This is so silly but maybe in the future we will work on an array
    return_type << "void";

    function_name << "_" << _function_symbol.get_name() << "_ext"
        ;

    bool has_ellipsis = false;
    ObjectList<Type> parameters = function_type.parameters(has_ellipsis);

    if (has_ellipsis)
    {
        _ostream << _funct_def.get_ast().get_locus() << ": warning: ellipsis is not valid when extending functions. Skipping" << std::endl;
        _extension_code = Source("");
    }
    else if (parameters.empty())
    {
        _ostream << _funct_def.get_ast().get_locus() << ": warning: function has zero parameters. Skipping" << std::endl;
        _extension_code = Source("");
    }
    else
    {
        if (!_extension_amount.is_constant())
        {
            extended_args << _extension_amount.get_type().get_declaration(_function_symbol.get_scope(), "_N");
        }

        DeclaredEntity declared_entity = _funct_def.get_declared_entity();

        ObjectList<ParameterDeclaration> param_decl = declared_entity.get_parameter_declarations(has_ellipsis);

        ReplaceSrcIdExpression replacements(_funct_def.get_scope_link());
        for (ObjectList<ParameterDeclaration>::iterator it = param_decl.begin();
                it != param_decl.end();
                it++)
        {
            IdExpression id_expr = it->get_name();
            Symbol sym = id_expr.get_computed_symbol();
            Type param_type = it->get_type();

            Type array_type = param_type.get_array_to(_extension_amount.get_ast(), _extension_amount.get_scope());

            extended_args.append_with_separator(
                    array_type.get_declaration(_function_symbol.get_scope(), id_expr),
                    ",");

            replacements.add_replacement(sym, "(" + sym.get_name() + ")[_i]");
        }

        Source replaced_body;
        extended_body
            << "{"
            <<   "int _i;"
            <<   "for (_i = 0; _i < " << _extension_amount << "; _i++)"
            <<   "{"
            <<   replacements.replace(_funct_def.get_function_body())
            <<   "}"
            << "}"
            ;

    }
}
