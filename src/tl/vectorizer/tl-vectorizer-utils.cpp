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

#include "tl-vectorizer.hpp"
#include "tl-vectorizer-utils.hpp"

namespace TL 
{ 
    namespace Vectorization 
    {
        namespace Utils
        {
            LookForReturnVisitor::LookForReturnVisitor()
            {
            }

            bool LookForReturnVisitor::join_list(ObjectList<bool>& list) 
            {
                for(ObjectList<bool>::const_iterator it = list.begin(); 
                        it != list.end();
                        it++)
                {
                    if ((*it) == true)
                        return true;
                }

                return false;
            }

            bool LookForReturnVisitor::visit(const Nodecl::ReturnStatement& n)
            {
                return true;
            }

            MaskCheckCostEstimation::MaskCheckCostEstimation()
                : 
                _add_cost(1),
                _minus_cost(1),
                _mul_cost(3),
                _div_cost(5),
                _return_cost(3),
                _if_statement_cost(4), 
                _else_statement_cost(1),
                _static_for_statement_cost(10),
                _masked_for_statement_cost(3),
                _function_call_cost(1000),
                _nesting_threshold(0)
            {
            }

            unsigned int MaskCheckCostEstimation::get_mask_check_cost(
                    const Nodecl::NodeclBase& n, unsigned int initial_cost,
                    const unsigned int cost_threshold)
            {
                if (initial_cost < cost_threshold)
                    _cost = initial_cost;
                else
                    _cost = 0;

                this->walk(n);

                return _cost;
            }

            void MaskCheckCostEstimation::binary_operation(const Nodecl::NodeclBase& n, 
                    const unsigned int cost)
            {
                _cost += cost;
                walk(n.as<Nodecl::Add>().get_lhs());
                walk(n.as<Nodecl::Add>().get_rhs());
            }

            void MaskCheckCostEstimation::visit(const Nodecl::Add& n)
            {
                binary_operation(n, _add_cost);
            }

            void MaskCheckCostEstimation::visit(const Nodecl::Minus& n)
            {
                binary_operation(n, _minus_cost);
            }
 
            void MaskCheckCostEstimation::visit(const Nodecl::Mul& n)
            {
                binary_operation(n, _mul_cost);
            }

            void MaskCheckCostEstimation::visit(const Nodecl::Div& n)
            {
                binary_operation(n, _div_cost);
            }

            void MaskCheckCostEstimation::visit(const Nodecl::ReturnStatement& n)
            {
                _cost += _return_cost;
                walk(n.get_value());
            }
 
            void MaskCheckCostEstimation::visit(const Nodecl::IfElseStatement& n)
            {
                _cost += _if_statement_cost + _else_statement_cost;

                if (_nesting_level < _nesting_threshold)
                {
                    _nesting_level++;
                    walk(n.get_then());
                    _nesting_level--;

                    if(!n.get_else().is_null())
                    {
                        _nesting_level++;
                        walk(n.get_else());
                        _nesting_level--;
                    }
                }
            }

            void MaskCheckCostEstimation::visit(const Nodecl::ForStatement& n)
            {
                _cost += _static_for_statement_cost;

                if (_nesting_level < _nesting_threshold)
                {
                    _nesting_level++;
                    walk(n.get_statement());
                    _nesting_level--;
                }
            }

            void MaskCheckCostEstimation::visit(const Nodecl::FunctionCall& n)
            {
                _cost += _function_call_cost;
            }



            Nodecl::NodeclBase get_new_mask_symbol(TL::Scope scope,
                    const int mask_size)
            {
                TL::Symbol new_mask_sym = scope.new_symbol("__mask_" + 
                        Vectorizer::_vectorizer->get_var_counter());
                new_mask_sym.get_internal_symbol()->kind = SK_VARIABLE;
                new_mask_sym.get_internal_symbol()->entity_specs.is_user_declared = 1;
                new_mask_sym.set_type(TL::Type::get_mask_type(mask_size));

                return new_mask_sym.make_nodecl(true, make_locus("", 0, 0));
            }

            Nodecl::NodeclBase emit_disjunction_mask(
                    const ObjectList<Nodecl::NodeclBase>& bb_exit_mask_list,
                    Nodecl::List& output_stmt_list,
                    TL::Scope& scope,
                    const int mask_size)
            {
                ObjectList<Nodecl::NodeclBase>::const_iterator it = bb_exit_mask_list.begin();

                Nodecl::NodeclBase lhs = *it;
                it++;

                while(it != bb_exit_mask_list.end())
                {
                    Nodecl::NodeclBase new_mask_sym_nodecl = get_new_mask_symbol(
                            scope, mask_size);

                    Nodecl::ExpressionStatement new_mask_exp =
                        Nodecl::ExpressionStatement::make(
                                Nodecl::VectorMaskAssignment::make(
                                    new_mask_sym_nodecl.shallow_copy(),
                                    Nodecl::VectorMaskOr::make(
                                        lhs.shallow_copy(),
                                        it->shallow_copy(),
                                        lhs.get_type(),
                                        make_locus("", 0, 0)),
                                    lhs.get_type(),
                                    make_locus("", 0, 0)));

                    output_stmt_list.append(new_mask_exp);

                    lhs = new_mask_sym_nodecl;
                    it++;
                }

                return lhs;
            }

            bool is_declared_in_scope(const scope_t *const  target_scope,
                    const scope_t *const symbol_scope)
            {
                if (symbol_scope == NULL)
                    return false;
                else if (target_scope == NULL)
                    return false;
                else if (target_scope == symbol_scope)
                    return true;
                else
                {
                    return false;
                }
            }

            bool is_all_one_mask(const Nodecl::NodeclBase& n)
            {
                if (n.is<Nodecl::MaskLiteral>())
                {
                    Nodecl::MaskLiteral ml = n.as<Nodecl::MaskLiteral>();

                    if (ml.is_constant())
                    {
                        if (const_value_is_minus_one(ml.get_constant()))
                            return true;
                    }
                }

                return false;
            }
        }
    }
}


