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

#include "tl-analysis-check-phase.hpp"
#include "tl-analysis-singleton.hpp"
#include "tl-analysis-utils.hpp"
#include "tl-pcfg-visitor.hpp"

#include <algorithm>

namespace TL {
namespace Analysis {
    
namespace {
    
    Nodecl::NodeclBase get_nodecl_from_string( std::string str, ReferenceScope sc )
    {
        Source src; src << str;
        return src.parse_expression( sc );
    }
    
    Nodecl::List extract_reaching_definitions_map_from_clause( const PragmaCustomClause& c, ReferenceScope sc )
    {
        Nodecl::List result;
        
        ObjectList<std::string> args = c.get_tokenized_arguments( ExpressionTokenizerTrim( ';' ) );
        for( ObjectList<std::string>::iterator it = args.begin( ); it != args.end( ); ++it )
        {   // Each token will have the form: "var : value-list"
            // Split the token using the ':'
            std::string token = *it;
            std::string::iterator end_pos = std::remove( token.begin( ), token.end( ), ' ' );
            token.erase( end_pos, token.end( ) );
            int colon_pos = token.find( ':' );
            std::string reach_def = token.substr( 0, colon_pos );
            std::string value = token.substr( colon_pos+1, token.size( )-colon_pos );
            
            // Parse the variable which is a reaching definition
            Nodecl::NodeclBase reach_def_nodecl = get_nodecl_from_string( reach_def, sc );
            
            // Parse the value/s set for this variable
            // Create the ReachDefExpr corresponding to a pair of <reach_def, value>
            std::string current_value;
            int pos = 0;
            while( value.find( ',', pos ) != std::string::npos )
            {
                current_value = value.substr( pos, value.find( ',', pos ) - pos );
                Nodecl::NodeclBase value_nodecl = get_nodecl_from_string( current_value, sc );
                result.append( Nodecl::Analysis::ReachDefExpr::make( reach_def_nodecl.shallow_copy( ), value_nodecl ) );
                
                pos = value.find( ',', pos ) + 1;
            }
            current_value = value.substr( pos, value.size( ) - pos );
            Nodecl::NodeclBase value_nodecl = get_nodecl_from_string( current_value, sc );
            result.append( Nodecl::Analysis::ReachDefExpr::make( reach_def_nodecl.shallow_copy( ), value_nodecl ) );
        }
        
        return result;
    }
    
    Nodecl::List extract_induction_variable_info_from_clause( const PragmaCustomClause& c, ReferenceScope sc )
    {   // Each token will have the form: "iv : lb : ub : stride "
        Nodecl::List result;
        
        ObjectList<std::string> args = c.get_tokenized_arguments( ExpressionTokenizerTrim( ';' ) );
        for( ObjectList<std::string>::iterator it = args.begin( ); it != args.end( ); ++it )
        {
            // Split the token using the ':'
            std::string token = *it;
            std::string::iterator end_pos = std::remove( token.begin( ), token.end( ), ' ' );
            token.erase( end_pos, token.end( ) );
            
            int colon_pos = token.find( ':' );
            std::string iv = token.substr( 0, colon_pos );
            colon_pos++;
            std::string lb = token.substr( colon_pos, token.find( ':', colon_pos )-colon_pos );
            colon_pos = token.find( ':', colon_pos ) + 1;
            std::string ub = token.substr( colon_pos, token.find( ':', colon_pos )-colon_pos );
            colon_pos = token.find( ':', colon_pos ) + 1;
            std::string stride = token.substr( colon_pos, token.find( ':', colon_pos )-colon_pos );
            
            Nodecl::NodeclBase iv_nodecl = get_nodecl_from_string( iv, sc );
            Nodecl::NodeclBase lb_nodecl = get_nodecl_from_string( lb, sc );
            Nodecl::NodeclBase ub_nodecl = get_nodecl_from_string( ub, sc );
            Nodecl::NodeclBase stride_nodecl = get_nodecl_from_string( stride, sc );
            
            result.append( Nodecl::Analysis::InductionVarExpr::make( iv_nodecl, lb_nodecl, ub_nodecl, stride_nodecl ) );
        }
        
        return result;
    }
    
    void check_task_synchronizations( Node* current )
    {
        if( !current->is_visited( ) )
        {
            current->set_visited( true );
            
            if( current->is_omp_task_creation_node( ) )
            {   // This nodes have two children, the task they create and the child that is sequentially executed
                ObjectList<Node*> children = current->get_children( );
                ERROR_CONDITION( children.size( ) != 2, 
                                 "A task creation node must have 2 children, the created task and "\
                                 "the node that is sequentially executed. "\
                                 "Task creation node %d has %d children", current->get_id( ), children.size( ) );
            }
            else if( current->is_omp_task_node( ) )
            {
                ObjectList<Node*> children = current->get_children( );
                ERROR_CONDITION( children.empty( ), 
                                 "Task %d is never synchronized", current->get_id( ) );
            }
        }
    }
    
    void compare_assert_set_with_analysis_set( Utils::ext_sym_set assert_set, Utils::ext_sym_set analysis_set, 
                                                      std::string locus_str, int node_id, 
                                                      std::string clause_name, std::string analysis_name )
    {
        if( !assert_set.empty( ) )
        {
            if( analysis_set.empty( ) )
            {
                internal_error( "%s: Assertion '%s(%s)' does not fulfill.\n"\
                                "There are no %s variables associated to node %d\n", 
                                locus_str.c_str( ), 
                                clause_name.c_str( ), Utils::prettyprint_ext_sym_set( assert_set, /*dot*/ false ).c_str( ), 
                                analysis_name.c_str( ), node_id );
            }
            else
            {
                Utils::ext_sym_set diff = Utils::ext_sym_set_difference( assert_set, analysis_set );
                if( !diff.empty( ) )
                {
                    internal_error( "%s: Assertion '%s(%s)' does not fulfill.\n"\
                                    "Expressions '%s' are no %s variables associated to node %d\n", 
                                    locus_str.c_str( ), 
                                    clause_name.c_str( ), Utils::prettyprint_ext_sym_set( assert_set, /*dot*/ false ).c_str( ),
                                    Utils::prettyprint_ext_sym_set( diff, /*dot*/ false ).c_str( ), 
                                    analysis_name.c_str( ), node_id );
                }
            }
        }
    }
    
    void compare_assert_map_with_analysis_map( Utils::ext_sym_map assert_map, Utils::ext_sym_map analysis_map, 
                                               std::string locus_str, int node_id, 
                                               std::string clause_name, std::string analysis_name )
    {
        if( !assert_map.empty( ) )
        {
            if( analysis_map.empty( ) )
            {
                internal_error( "%s: Assertion 'reaching_definition_in(%s)' does not fulfill.\n"\
                                "There are no Input Reaching Definitions associated to node %d\n", 
                                locus_str.c_str( ), 
                                Utils::prettyprint_ext_sym_map( assert_map, /*dot*/ false ).c_str( ), 
                                node_id );
            }
            else
            {
                Nodecl::List rd_visited;
                for( Utils::ext_sym_map::iterator it = assert_map.begin( ); 
                    it != assert_map.end( ); ++it )
                {
                    Nodecl::NodeclBase expr = it->first.get_nodecl( );
                    if( !Nodecl::Utils::nodecl_is_in_nodecl_list( expr, rd_visited ) )
                    {
                        rd_visited.append( expr );
                        
                        // Get all values possible for the current expression
                        std::pair<Utils::ext_sym_map::iterator, Utils::ext_sym_map::iterator> assert_rd;
                        assert_rd = assert_map.equal_range( expr );
                        int assert_rd_size = assert_map.count( expr );
                        
                        std::pair<Utils::ext_sym_map::iterator, Utils::ext_sym_map::iterator> rd;
                        rd = analysis_map.equal_range( expr );
                        int rd_size = analysis_map.count( expr );
                        
                        if( assert_rd_size == rd_size )
                        {   // Check whether the values are the same
                            for( Utils::ext_sym_map::iterator it_r = assert_rd.first; it_r != assert_rd.second; ++it_r )
                            {
                                Nodecl::NodeclBase value = it_r->second;
                                bool found = false;
                                for( Utils::ext_sym_map::iterator it_s = rd.first; it_s != rd.second && !found; ++it_s )
                                {
                                    if( Nodecl::Utils::equal_nodecls( value, it_s->second ) )
                                        found = true;
                                }
                                if( !found )
                                {
                                    internal_error( "%s: Assertion 'reaching_definition_in(%s)' does not fulfill.\n"\
                                                    "Variable '%s' do not have the value '%s' in the set of reaching definitions "\
                                                    "computed during the analysis for node %d\n", 
                                                    locus_str.c_str( ), Utils::prettyprint_ext_sym_map( assert_map, /*dot*/ false ).c_str( ),
                                                    expr.prettyprint( ).c_str( ), value.prettyprint( ).c_str( ), node_id );
                                }
                            }
                        }
                        else
                        {
                            int i = 0;
                            std::string rd_str = "";
                            for( Utils::ext_sym_map::iterator it_r = rd.first; it_r != rd.second; ++it_r, ++i )
                            {
                                rd_str += it_r->second.prettyprint( );
                                if( i < rd_size-1 )
                                    rd_str += ", ";
                            }
                            
                            internal_error( "%s: Assertion 'reaching_definition_in(%s)' does not fulfill.\n"\
                                            "The values for variable '%s' computed during the analysis for node %d are '%s'\n", 
                                            locus_str.c_str( ), Utils::prettyprint_ext_sym_map( assert_map, /*dot*/ false ).c_str( ),
                                            expr.prettyprint( ).c_str( ), node_id, rd_str.c_str( ) );
                        }
                    }
                }
            }
        }
    }
    
    void check_assertions_rec( Node* current )
    {
        if( !current->is_visited( ) )
        {
            current->set_visited( true );
            
            // Treat current node
            std::string locus_str;
            if( current->is_graph_node( ) )
                locus_str = current->get_graph_label( ).get_locus_str( );
            else
            {
                ObjectList<Nodecl::NodeclBase> stmts = current->get_statements( );
                if( !stmts.empty( ) )
                    locus_str = stmts[0].get_locus_str( );
            }
                
            // Check UseDef analysis
            if( current->has_usage_assertion( ) )
            {
                Utils::ext_sym_set assert_ue = current->get_assert_ue_vars( );
                Utils::ext_sym_set assert_killed = current->get_assert_killed_vars( );
                Utils::ext_sym_set ue = current->get_ue_vars( );
                Utils::ext_sym_set killed = current->get_killed_vars( );
            
                compare_assert_set_with_analysis_set( assert_ue, ue, locus_str, current->get_id( ), "upper_exposed", "Upper Exposed" );
                compare_assert_set_with_analysis_set( assert_killed, killed, locus_str, current->get_id( ), "defined", "Killed" );
            }
                
            // Check Liveness analysis
            if( current->has_liveness_assertion( ) )
            {
                Utils::ext_sym_set assert_live_in = current->get_assert_live_in_vars( );
                Utils::ext_sym_set assert_live_out = current->get_assert_live_out_vars( );
                Utils::ext_sym_set assert_dead = current->get_assert_dead_vars( );
                Utils::ext_sym_set live_in = current->get_live_in_vars( );
                Utils::ext_sym_set live_out = current->get_live_out_vars( );
            
                compare_assert_set_with_analysis_set( assert_live_in, live_in, locus_str, current->get_id( ), "live_in", "Live In" );
                compare_assert_set_with_analysis_set( assert_live_out, live_out, locus_str, current->get_id( ), "live_out", "Live Out" );
                // Dead variables checking behaves a bit different, since we don't have a 'dead' set associated to each node
                if( !assert_dead.empty( ) ) 
                {
                    Utils::ext_sym_set diff = Utils::ext_sym_set_difference( assert_dead, live_in );
                    for( Utils::ext_sym_set::iterator it = assert_dead.begin( ); it != assert_dead.end( ); ++it )
                    {
                        if( Utils::ext_sym_set_contains_nodecl( it->get_nodecl( ), live_in ) )
                        {
                            internal_error( "%s: Assertion 'dead(%s)' does not fulfill.\n"\
                                            "Expression '%s' is not Dead at the Entry point of node %d\n", 
                                            locus_str.c_str( ), 
                                            Utils::prettyprint_ext_sym_set( assert_dead, /*dot*/ false ).c_str( ),
                                            it->get_nodecl( ).prettyprint( ).c_str( ),
                                            current->get_id( ) );
                        }
                    }
                }
            }
                
            // Check Reaching Definitions analysis
            if( current->has_reach_defs_assertion( ) )
            {
                Utils::ext_sym_map assert_reach_defs_in = current->get_assert_reaching_definitions_in( );
                Utils::ext_sym_map assert_reach_defs_out = current->get_assert_reaching_definitions_out( );
                Utils::ext_sym_map reach_defs_in = current->get_reaching_definitions_in( );
                Utils::ext_sym_map reach_defs_out = current->get_reaching_definitions_out( );
            
                compare_assert_map_with_analysis_map( assert_reach_defs_in, reach_defs_in, locus_str, current->get_id( ), 
                                                        "reaching_definition_in", "Input Reaching Definitions" );
                compare_assert_map_with_analysis_map( assert_reach_defs_out, reach_defs_out, locus_str, current->get_id( ), 
                                                        "reaching_definition_out", "Output Reaching Definitions" );
            }
                
            // Induction Variables
            if( current->has_induction_vars_assertion( ) )
            {
                ObjectList<Utils::InductionVariableData*> assert_induction_vars = current->get_assert_induction_vars( );
                if( current->is_loop_node( ) )
                {
                    ObjectList<Utils::InductionVariableData*> induction_vars = current->get_induction_variables( );
                
                    if( !assert_induction_vars.empty( ) )
                    {
                        for( ObjectList<Utils::InductionVariableData*>::iterator it = assert_induction_vars.begin( );
                            it != assert_induction_vars.end( ); ++it )
                        {
                            Utils::InductionVariableData* iv = *it;
                            Nodecl::NodeclBase iv_nodecl = iv->get_variable( ).get_nodecl( );
                            bool found = false;
                            for( ObjectList<Utils::InductionVariableData*>::iterator it2 = induction_vars.begin( );
                                    it2 != induction_vars.end( ) && !found; ++it2 )
                            {
                                if( Nodecl::Utils::equal_nodecls( ( *it2 )->get_variable( ).get_nodecl( ), iv_nodecl ) )
                                {
                                    found = true;
                                    
                                    if( !Nodecl::Utils::equal_nodecls( ( *it2 )->get_lb( ), iv->get_lb( ) ) )
                                    {
                                        internal_error( "%s: Assertion 'induction_var(%s)' does not fulfill.\n"\
                                                        "Lower Bound computed for induction variable '%s' "\
                                                        "in node %d is '%s', but the lower bound indicated in the assertion is '%s'.\n", 
                                                        locus_str.c_str( ), Utils::prettyprint_induction_vars( assert_induction_vars ).c_str( ), 
                                                        iv_nodecl.prettyprint( ).c_str( ), current->get_id( ), 
                                                        ( *it2 )->get_lb( ).prettyprint( ).c_str( ), 
                                                        iv->get_lb( ).prettyprint( ).c_str( ) );
                                    }
                                    else if( !Nodecl::Utils::equal_nodecls( ( *it2 )->get_ub( ), iv->get_ub( ) ) )
                                    {
                                        internal_error( "%s: Assertion 'induction_var(%s)' does not fulfill.\n"\
                                                        "Upper Bound computed for induction variable '%s' "\
                                                        "in node %d is '%s', but the upper bound indicated in the assertion is '%s'.\n", 
                                                        locus_str.c_str( ), Utils::prettyprint_induction_vars( assert_induction_vars ).c_str( ), 
                                                        iv_nodecl.prettyprint( ).c_str( ), current->get_id( ), 
                                                        ( *it2 )->get_ub( ).prettyprint( ).c_str( ), 
                                                        iv->get_ub( ).prettyprint( ).c_str( ) );
                                    }
                                    else if( !Nodecl::Utils::equal_nodecls( ( *it2 )->get_increment( ), iv->get_increment( ) ) )
                                    {
                                        internal_error( "%s: Assertion 'induction_var(%s)' does not fulfill.\n"\
                                                        "Stride computed for induction variable '%s' "\
                                                        "in node %d is '%s', but the stride indicated in the assertion is '%s'.\n", 
                                                        locus_str.c_str( ), Utils::prettyprint_induction_vars( assert_induction_vars ).c_str( ), 
                                                        iv_nodecl.prettyprint( ).c_str( ), current->get_id( ), 
                                                        ( *it2 )->get_increment( ).prettyprint( ).c_str( ), 
                                                        iv->get_increment( ).prettyprint( ).c_str( ) );
                                    }
                                }
                            }
                            if( !found )
                            {
                                internal_error( "%s: Assertion 'induction_var(%s)' does not fulfill.\n"\
                                                "Induction variable '%s' not found in the induction variables list "\
                                                "of node %d\n", 
                                                locus_str.c_str( ), Utils::prettyprint_induction_vars( assert_induction_vars ).c_str( ), 
                                                iv_nodecl.prettyprint( ).c_str( ), current->get_id( ) );
                            }
                        }
                    }
                }
                else
                {
                    if( !assert_induction_vars.empty( ) )
                    {
                        WARNING_MESSAGE( "%s: warning: #pragma analysis_check assert induction_variables is only used "\
                                            "when associated with a loop structure. Ignoring it when associated with any other statement.",
                                            locus_str.c_str( ) );
                    }
                }
            }
                
            // Auto-scoping
            if( current->has_autoscope_assertion( ) )
            {
                // Autoscope is particular because the computed auto-scope is not in the current node (the task creation node), 
                // but in his task child node, which is the actual task
                ObjectList<Node*> children = current->get_children( );
                ERROR_CONDITION( children.size( ) > 2, "A task creation node should have, at least 1 child, the created task, "\
                                 "and at most, 2 children, the created task and the following node in the sequential execution flow. "\
                                 "Nonetheless task %d has %d children.", current->get_id( ), children.size( ) );
                Node* task = ( children[0]->is_omp_task_node( ) ? children[0] : children[1] );
                Utils::ext_sym_set assert_autosc_firstprivate = current->get_assert_auto_sc_firstprivate_vars( );
                Utils::ext_sym_set assert_autosc_private = current->get_assert_auto_sc_private_vars( );
                Utils::ext_sym_set assert_autosc_shared = current->get_assert_auto_sc_shared_vars( );
                Utils::ext_sym_set autosc_firstprivate = task->get_sc_firstprivate_vars( );
                Utils::ext_sym_set autosc_private = task->get_sc_private_vars( );
                Utils::ext_sym_set autosc_shared = task->get_sc_shared_vars( );
                
                // TODO
                compare_assert_set_with_analysis_set( assert_autosc_firstprivate, autosc_firstprivate, 
                                                      locus_str, task->get_id( ), "auto_sc_firstprivate", "AutoScope Firstprivate" );
                compare_assert_set_with_analysis_set( assert_autosc_private, autosc_private, 
                                                      locus_str, task->get_id( ), "auto_sc_private", "AutoScope Private" );
                compare_assert_set_with_analysis_set( assert_autosc_shared, autosc_shared, 
                                                      locus_str, task->get_id( ), "auto_sc_shared", "AutoScope Shared" );
                
            }
            
            
            // Recursively visit inner nodes
            if( current->is_graph_node( ) )
            {
                check_assertions_rec( current->get_graph_entry_node( ) );
            }
            
            // Recursively visit current children
            ObjectList<Node*> children = current->get_children( );
            for( ObjectList<Node*>::iterator it = children.begin( ); it != children.end( ); ++it )
            {
                check_assertions_rec( *it );
            }
        }
    }
}
    
    AnalysisCheckPhase::AnalysisCheckPhase( )
        : PragmaCustomCompilerPhase("analysis_check")
    {
        set_phase_name( "Phase checking the correctness of different analysis" );
        set_phase_description( "This phase checks first the robustness of a PCFG and then "\
                                " the correctness of different analysis based on user defined pragmas." );
        
        // Register constructs
        register_construct("assert");
        
        dispatcher( ).statement.pre["assert"].connect( functor( &AnalysisCheckPhase::assert_handler_pre, *this ) );
        dispatcher( ).statement.post["assert"].connect( functor( &AnalysisCheckPhase::assert_handler_post, *this ) );
    }

    void AnalysisCheckPhase::assert_handler_pre( TL::PragmaCustomStatement directive )
    {   // Nothing to be done
    }
    
    void AnalysisCheckPhase::assert_handler_post( TL::PragmaCustomStatement directive )
    {   // TODO
        Nodecl::List environment;
        PragmaCustomLine pragma_line = directive.get_pragma_line( );
        const locus_t* loc = directive.get_locus( );
        
        // Use-Def analysis clauses
        // #pragma analysis_check assert upper_exposed(expr-list)
        if( pragma_line.get_clause( "upper_expposed" ).is_defined( ) )
        {
            PragmaCustomClause upper_exposed_clause = pragma_line.get_clause( "upper_expposed" );
            
            environment.append(
                Nodecl::Analysis::UpperExposed::make(
                    Nodecl::List::make( upper_exposed_clause.get_arguments_as_expressions( ) ), loc ) );
        }
        if( pragma_line.get_clause( "defined" ).is_defined( ) )
        {
            PragmaCustomClause defined_clause = pragma_line.get_clause( "defined" );
            
            environment.append(
                Nodecl::Analysis::Defined::make(
                    Nodecl::List::make( defined_clause.get_arguments_as_expressions( ) ), loc ) );
        }
        
        // Liveness analysis clauses
        // #pragma analysis_check assert live_in(expr-list)
        if( pragma_line.get_clause( "live_in" ).is_defined( ) )
        {
            PragmaCustomClause live_in_clause = pragma_line.get_clause( "live_in" );
            
            environment.append(
                Nodecl::Analysis::LiveIn::make(
                    Nodecl::List::make( live_in_clause.get_arguments_as_expressions( ) ), loc ) );
        }
        if( pragma_line.get_clause( "live_out" ).is_defined( ) )
        {
            PragmaCustomClause live_out_clause = pragma_line.get_clause( "live_out" );
            
            environment.append(
                Nodecl::Analysis::LiveOut::make(
                    Nodecl::List::make( live_out_clause.get_arguments_as_expressions( ) ), loc ) );
        }
        if( pragma_line.get_clause( "dead" ).is_defined( ) )
        {
            PragmaCustomClause dead_clause = pragma_line.get_clause( "dead" );
            
            environment.append(
                Nodecl::Analysis::Dead::make(
                    Nodecl::List::make( dead_clause.get_arguments_as_expressions( ) ), loc ) );
        }
        
        // Reaching definition analysis clauses
        // #pragma analysis_check assert reaching_definition_in(<expr:expr-list>-list)
        if( pragma_line.get_clause( "reaching_definition_in" ).is_defined( ) )
        {
            PragmaCustomClause reach_defs_in_clause = pragma_line.get_clause( "reaching_definition_in" );
            Nodecl::List reach_defs_in = 
                extract_reaching_definitions_map_from_clause( reach_defs_in_clause, 
                                                              pragma_line.retrieve_context( ) );
            
            environment.append( Nodecl::Analysis::ReachingDefinitionIn::make( reach_defs_in, loc ) );
        }
        if( pragma_line.get_clause( "reaching_definition_out" ).is_defined( ) )
        {
            PragmaCustomClause reach_defs_out_clause = pragma_line.get_clause( "reaching_definition_out" );
            
            Nodecl::List reach_defs_out = 
                extract_reaching_definitions_map_from_clause( reach_defs_out_clause, 
                                                              pragma_line.retrieve_context( ) );
            
            environment.append( Nodecl::Analysis::ReachingDefinitionOut::make( reach_defs_out, loc ) );
        }
        
        // Induction variables analysis clauses
        if( pragma_line.get_clause( "induction_var" ).is_defined( ) )
        {
            PragmaCustomClause induction_vars_clause = pragma_line.get_clause( "induction_var" );
            
            Nodecl::List induction_vars = 
                extract_induction_variable_info_from_clause( induction_vars_clause, 
                                                             pragma_line.retrieve_context( ) );
            
            environment.append( Nodecl::Analysis::InductionVariable::make( induction_vars, loc ) );
        }
        
        // Auto-scope analysis clauses
        if( pragma_line.get_clause( "auto_sc_firstprivate" ).is_defined( ) )
        {
            PragmaCustomClause auto_sc_fp_vars_clause = pragma_line.get_clause( "auto_sc_firstprivate" );
            
            environment.append(
                Nodecl::Analysis::AutoScope::Firstprivate::make(
                    Nodecl::List::make( auto_sc_fp_vars_clause.get_arguments_as_expressions( ) ), loc ) );
        }
        if( pragma_line.get_clause( "auto_sc_private" ).is_defined( ) )
        {
            PragmaCustomClause auto_sc_p_vars_clause = pragma_line.get_clause( "auto_sc_private" );
            
            environment.append(
                Nodecl::Analysis::AutoScope::Private::make(
                    Nodecl::List::make( auto_sc_p_vars_clause.get_arguments_as_expressions( ) ), loc ) );
        }
        if( pragma_line.get_clause( "auto_sc_shared" ).is_defined( ) )
        {
            PragmaCustomClause auto_sc_s_vars_clause = pragma_line.get_clause( "auto_sc_shared" );
            
            environment.append(
                Nodecl::Analysis::AutoScope::Shared::make(
                    Nodecl::List::make( auto_sc_s_vars_clause.get_arguments_as_expressions( ) ), loc ) );
        }
        
        Nodecl::Analysis::Assert assert =
            Nodecl::Analysis::Assert::make(
                directive.get_statements( ),
                environment,
                directive.get_locus( ) );
        
        pragma_line.diagnostic_unused_clauses();
        directive.replace( assert );
    }
    
    void AnalysisCheckPhase::run( TL::DTO& dto )
    {
        PragmaCustomCompilerPhase::run(dto);
        
        AnalysisSingleton& analysis = AnalysisSingleton::get_analysis( );
        PCFGAnalysis_memento memento;

        Nodecl::NodeclBase ast = dto["nodecl"];

        ObjectList<ExtensibleGraph*> pcfgs;
            
        // Auto Scope analysis encloses all other analysis
        // FIXME we should launch the analyses depending on the clauses in the assert directives
        pcfgs = analysis.all_analyses( memento, ast );
        
        // Check PCFG consistency
        for( ObjectList<ExtensibleGraph*>::iterator it = pcfgs.begin( ); it != pcfgs.end( ); ++it )
        {
            if( VERBOSE )
                printf( "Check PCFG '%s' consistency\n", ( *it )->get_name( ).c_str( ) );
            check_pcfg_consistency( *it );
        }
        // Check user assertions
        for( ObjectList<ExtensibleGraph*>::iterator it = pcfgs.begin( ); it != pcfgs.end( ); ++it )
        {
            analysis.print_pcfg( memento, (*it)->get_name( ) );
            
            if( VERBOSE )
                printf( "Check analysis assertions of PCFG '%s'\n", ( *it )->get_name( ).c_str( ) );
            check_analysis_assertions( *it );
        }
        
        // Remove the nodes included in this 
        AnalysisCheckVisitor v;
        v.walk( ast );
    }
    
    void AnalysisCheckPhase::check_pcfg_consistency( ExtensibleGraph* graph )
    {
        Node* graph_node = graph->get_graph( );
        check_task_synchronizations( graph_node );
        ExtensibleGraph::clear_visits( graph_node );
        
    }
    
    void AnalysisCheckPhase::check_analysis_assertions( ExtensibleGraph* graph )
    {
        Node* graph_node = graph->get_graph( );
        check_assertions_rec( graph_node );
        ExtensibleGraph::clear_visits( graph_node );
    }
    
    void AnalysisCheckVisitor::visit( const Nodecl::Analysis::Assert& n )
    {
        Nodecl::Utils::remove_from_enclosing_list( n );
    }
}
}

EXPORT_PHASE(TL::Analysis::AnalysisCheckPhase);
