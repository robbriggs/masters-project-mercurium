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
#include "tl-decl_closure.hpp"
#include "tl-pragmasupport.hpp"

#include "tl-declarationclosure.hpp"

/*
 * Example using the declaration closure of a type. Basically it returns a
 * source that declares everything needed to declare the type of a given symbol
 */


namespace TL
{
    class DeclClosurePragma : public PragmaCustomCompilerPhase
    {
        private:
        public:
            DeclClosurePragma()
                : PragmaCustomCompilerPhase("mypragma")
            {
                set_phase_name("Example phase using closure declaration");

                register_directive("closure");
                on_directive_pre["closure"].connect(functor(&DeclClosurePragma::closure_pre, *this));

                register_directive("test");
                on_directive_pre["test"].connect(functor(&DeclClosurePragma::test_pre, *this));
            }

            void test_pre(PragmaCustomConstruct pragma_custom_construct)
            {
                if (pragma_custom_construct.is_parameterized())
                {
                    std::cerr << "Parameterized" << std::endl;
                    ObjectList<std::string> parameters = pragma_custom_construct.get_parameter_arguments();

                    for (ObjectList<std::string>::iterator it = parameters.begin();
                            it != parameters.end();
                            it++)
                    {
                        std::cerr << "-> '" << *it << "'" << std::endl;
                    }
                }
                else
                {
                    std::cerr << "Not parameterized" << std::endl;
                }
            }

            void closure_pre(PragmaCustomConstruct pragma_custom_construct)
            {
                PragmaCustomClause clause = pragma_custom_construct.get_clause("symbols");
                ObjectList<IdExpression> id_expressions = clause.id_expressions();

                for (ObjectList<IdExpression>::iterator it = id_expressions.begin();
                        it != id_expressions.end();
                        it++)
                {
                    DeclarationClosure decl_closure(pragma_custom_construct.get_scope_link());

                    decl_closure.add(it->get_symbol());

                    std::cerr << "CLOSURE of '" << it->prettyprint() << "' is " << std::endl;
                    std::cerr << "---- Begin" << std::endl;
                    std::cerr << decl_closure.closure().get_source();
                    std::cerr << "---- End" << std::endl;
                }
            }
    };
}

EXPORT_PHASE(TL::DeclClosurePragma);

