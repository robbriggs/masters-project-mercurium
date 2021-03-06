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

#ifndef TL_IV_ANALYSIS_HPP
#define TL_IV_ANALYSIS_HPP

#include "tl-extensible-graph.hpp"
#include "tl-induction-variables-data.hpp"
#include "tl-nodecl.hpp"
#include "tl-nodecl-utils.hpp"
#include "tl-nodecl-visitor.hpp"
#include "tl-symbol.hpp"

namespace TL {
namespace Analysis {

    // ********************************************************************************************* //
    // ************************** Class for induction variables analysis *************************** //

    class LIBTL_CLASS InductionVariableAnalysis : public Nodecl::ExhaustiveVisitor<void> {
    private:

        // Variables for Induction Variables analysis
        Utils::InductionVarsPerNode _induction_vars;
        ExtensibleGraph* _graph;

        // Variables for modified Nodecl visitor
        Nodecl::NodeclBase _constant;           /*!< Nodecl to be checked of being constant */
        bool _defining;                         /*!< Boolean used during the visit indicating whether we are in a defining context */
        bool _is_induction_var;                 /*!< Boolean used during the visit indicating whether a nodecl is an induction variable */

        //! Recursive method that actually computes the induction variables of \_graph
        void compute_induction_variables_rec( Node* current );

        void detect_basic_induction_variables(Node* node, Node* loop);
        void detect_derived_induction_variables( Node* node, Node* loop );

        bool is_there_unique_definition_in_loop( Nodecl::NodeclBase iv_st, Node* iv_node, Node* loop );
        bool is_there_definition_in_loop_(Nodecl::NodeclBase iv_st, Node* iv_node, Node* current, Node* loop );

        /*!This method returns true when a potential IV is a real IV within a loop
         * This means that no other modifications of the variable make it not be an IV and
         * also that the variable is not private in case it is within a parallel or simd region
         * The method might recompute the increment of the IV in case it is necessary
         * @return True, when the variable ends up being a real Induction Variable
         */
        bool check_potential_induction_variable( const Nodecl::NodeclBase& iv, Nodecl::NodeclBase& incr,
                                                 ObjectList<Nodecl::NodeclBase>& incr_list,
                                                 const Nodecl::NodeclBase& stmt, Node* loop );

        /*!This method returns true when a potential induction variable is decided not to be an IV
         * because it is modified in different positions inside the loop causing the variable not to 
         * fulfill the restrictions of an induction variable
         */
        bool check_undesired_modifications( const Nodecl::NodeclBase& iv, Nodecl::NodeclBase& incr,
                                            ObjectList<Nodecl::NodeclBase>& incr_list,
                                            const Nodecl::NodeclBase& stmt, Node* node, Node* loop );

        /*!This method returns true when a potential induction variable is always accessing the same memory location.
         * With this we avoid considering as induction variables expressions like: a[b[x]]
         */
        bool check_constant_memory_access( const Nodecl::NodeclBase& iv, Node* loop );

    public:

        // **** Constructor **** //

        InductionVariableAnalysis( ExtensibleGraph* graph );

        // **** Induction Variables analysis methods **** //

        /*!Compute the set of induction variables of a given PCFG
         * An induction variable is the variable that gets increased or decreased by
         * a fixed amount on every iteration of a loop, or is a linear function of
         * another induction variable.
         */
        void compute_induction_variables( );

        Nodecl::NodeclBase is_basic_induction_variable( Nodecl::NodeclBase st, Node* loop,
                                                        Nodecl::NodeclBase& incr, 
                                                        ObjectList<Nodecl::NodeclBase>& incr_list );

        Nodecl::NodeclBase is_derived_induction_variable( Nodecl::NodeclBase st, Node* current,
                                                          Node* loop, Nodecl::NodeclBase& family );

        Utils::InductionVarsPerNode get_all_induction_vars( ) const;
    };

    // ************************ END class for induction variables analysis ************************* //
    // ********************************************************************************************* //



    // ********************************************************************************************* //
    // ****************** Visitor that checks whether a potential IV is a real IV ****************** //

    class LIBTL_CLASS FalseInductionVariablesVisitor : public Nodecl::ExhaustiveVisitor<void>
    {
    private:
        // Input info
        Nodecl::NodeclBase _iv;
        Nodecl::NodeclBase* _incr;
        ObjectList<Nodecl::NodeclBase>* _incr_list;
        Node* _loop;

        // Output info
        bool _is_induction_var;

        // Members convenient during visiting
        int _n_nested_conditionals;     /*!< Number of conditionals that contains the statement currently parsed */

        Nodecl::Calculator _calc;

        //! Resets the class members as if the partially computed IV was never an Induction Variable
        void undefine_induction_variable( );

    public:
        // *** Constructor *** //
        FalseInductionVariablesVisitor( Nodecl::NodeclBase iv, Nodecl::NodeclBase *incr, 
                                        ObjectList<Nodecl::NodeclBase>* incr_list, Node* loop );

        // *** Getters and Setters*** //
        bool get_is_induction_variable( ) const;

        // *** Visiting methods *** //
        Ret join_list( TL::ObjectList<bool>& list );

        Ret unhandled_node( const Nodecl::NodeclBase& n );
        
        Ret visit( const Nodecl::AddAssignment& n );
        Ret visit( const Nodecl::ArithmeticShrAssignment& n );
        Ret visit( const Nodecl::Assignment& n );
        Ret visit( const Nodecl::BitwiseAndAssignment& n );
        Ret visit( const Nodecl::BitwiseOrAssignment& n );
        Ret visit( const Nodecl::BitwiseShlAssignment& n );
        Ret visit( const Nodecl::BitwiseShrAssignment& n );
        Ret visit( const Nodecl::BitwiseXorAssignment& n );
        Ret visit( const Nodecl::ConditionalExpression& n );
        Ret visit( const Nodecl::DivAssignment& n );
        Ret visit( const Nodecl::IfElseStatement& n );
        Ret visit( const Nodecl::MinusAssignment& n );
        Ret visit( const Nodecl::ModAssignment& n );
        Ret visit( const Nodecl::MulAssignment& n );
        Ret visit( const Nodecl::Postdecrement& n );
        Ret visit( const Nodecl::Postincrement& n );
        Ret visit( const Nodecl::Predecrement& n );
        Ret visit( const Nodecl::Preincrement& n );
    };

    // **************** END Visitor that checks whether a potential IV is a real IV **************** //
    // ********************************************************************************************* //
}
}

#endif          // TL_IV_ANALYSIS_HPP