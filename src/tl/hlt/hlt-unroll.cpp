/*
    Mercurium C/C++ Compiler
    Copyright (C) 2006-2009 - Roger Ferrer Ibanez <roger.ferrer@bsc.es>
    Barcelona Supercomputing Center - Centro Nacional de Supercomputacion
    Universitat Politecnica de Catalunya

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*/
#include "hlt-unroll.hpp"
#include <sstream>

using namespace TL::HLT;

TL::Source LoopUnroll::get_source()
{
    // Nothing at the moment
    return do_unroll();
}

LoopUnroll::LoopUnroll(ForStatement for_stmt, unsigned int factor)
     : _for_stmt(for_stmt), _factor(factor), _regular(true), _with_epilog(false)
{
    if (_for_stmt.regular_loop())
    {
        _regular = false;
    }
}

TL::Source LoopUnroll::do_unroll()
{
    if (_regular)
    {
        // Do nothing if the given loop was not regular
        std::cerr << _for_stmt.get_ast().get_locus() 
            << ": warning: is not a regular loop, unroll will not be applied" 
            << std::endl;

        return _for_stmt.prettyprint();
    }

    // Get parts of the loop
    IdExpression induction_var = _for_stmt.get_induction_variable();
    Expression lower_bound = _for_stmt.get_lower_bound();
    Expression upper_bound = _for_stmt.get_upper_bound();
    Expression step = _for_stmt.get_step();
    TL::Source operator_bound = _for_stmt.get_bound_operator();

    Statement loop_body = _for_stmt.get_loop_body();

    TL::Source result, epilogue, main;

    result
        << "{"
        << main
        << epilogue
        << "}"
        ;

    Source replicated_body;
    main
        << "for (" << induction_var << " = " << lower_bound << ";"
                   << induction_var << operator_bound << "((" << upper_bound << ") - " << _factor << ") ;"
                   << induction_var << "+= (" << step << ") * " << _factor << ")"
        << "{"
        << replicated_body
        << "}"
        ;

    // FIXME - It could help to initialize here another variable and make both loops independent
    epilogue
        << "for ( ; "  // No initialization, keep using the old induction var
                   << induction_var << operator_bound << upper_bound << ";"
                   << induction_var << "+= (" << step << "))"
                   << loop_body
        ;

    // Replicate the body
    for (unsigned int i = 0; i < _factor; i++)
    {
        ReplaceIdExpression replacement;
        if (i > 0)
        {
            std::stringstream ss;
            ss << induction_var << " + " << i;
            replacement.add_replacement(induction_var.get_symbol(), ss.str());
        }

        Statement replaced_body = replacement.replace(loop_body);
        replicated_body
            << replaced_body
            ;
    }

    return result;
}
