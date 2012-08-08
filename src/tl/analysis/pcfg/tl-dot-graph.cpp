/*--------------------------------------------------------------------
  (C) Copyright 2006-2012 Barcelona Supercomputing Center
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



#include <fstream>
#include <sstream>
#include <sys/stat.h>
#include <unistd.h>

#include "cxx-codegen.h"
#include "tl-extensible-graph.hpp"

namespace TL {
namespace Analysis {

    static void makeup_dot_block( std::string& str );
    static std::string prettyprint_reaching_definitions( nodecl_map syms_def );
    static std::string prettyprint_ext_sym_set(  Utils::ext_sym_set s );

    void ExtensibleGraph::print_graph_to_dot( )
    {
        std::ofstream dot_cfg;

        char buffer[1024];
        getcwd(buffer, 1024);
        std::stringstream ss; ss << rand( );

        // Create the directory of dot files if necessary and the new dot file
        struct stat st;
        std::string directory_name = std::string(buffer) + "/dot/";
        if( stat(directory_name.c_str( ), &st) != 0 )
        {
            int dot_directory = mkdir( directory_name.c_str( ), S_IRWXU );
            if( dot_directory != 0 )
            {
                internal_error ( "An error occurred while creating the dot files directory in '%s'", directory_name.c_str( ) );
            }
        }
        std::string dot_file_name = directory_name + _name /*+ ss.str( )*/ + ".dot";
        dot_cfg.open( dot_file_name.c_str( ) );

        // Create the dog graphs
        if( dot_cfg.good( ) )
        {
            if( CURRENT_CONFIGURATION->debug_options.analysis_verbose ||
                CURRENT_CONFIGURATION->debug_options.enable_debug_code ||
                CURRENT_CONFIGURATION->debug_options.print_pcfg )
                std::cerr << "   ==> File '" << dot_file_name << "'" << std::endl;

            int subgraph_id = 0;
            dot_cfg << "digraph CFG {\n";
                std::string graph_data = "";
                std::vector<std::string> outer_edges;
                std::vector<Node*> outer_nodes;
                get_nodes_dot_data( _graph, graph_data, outer_edges, outer_nodes, "\t", subgraph_id );
                dot_cfg << graph_data;
            dot_cfg << "}\n";

            ExtensibleGraph::clear_visits( _graph );

            dot_cfg.close( );

            if( !dot_cfg.good( ) )
            {
                internal_error ("Unable to close the file '%s' where CFG has been stored.", dot_file_name.c_str( ) );
            }
        }
        else
        {
            internal_error ("Unable to open the file '%s' to store the CFG.", dot_file_name.c_str( ) );
        }
    }

    // Preorder traversal
    void ExtensibleGraph::get_nodes_dot_data( Node* current, std::string& dot_graph,
                                              std::vector<std::string>& outer_edges, std::vector<Node*>& outer_nodes,
                                             std::string indent, int& subgraph_id )
    {
        if( !current->is_visited( ) )
        {
            current->set_visited(true);
            if( current->is_graph_node( ) )
            {
                std::stringstream ssgid; ssgid << subgraph_id;
                std::stringstream ssnode; ssnode << current->get_id( );
                std::string subgraph_label = ssnode.str( ) + " ";
                Nodecl::NodeclBase actual_label(current->get_graph_label( ) );
                if(!actual_label.is_null( ) )
                {
                    subgraph_label += codegen_to_str(actual_label.get_internal_nodecl( ),
                            nodecl_retrieve_context(actual_label.get_internal_nodecl( ) ) );
//                         actual_label.get_text( );
                }

                std::string live_in = prettyprint_ext_sym_set( current->get_live_in_vars( ) );
                std::string live_out = prettyprint_ext_sym_set( current->get_live_out_vars( ) );
                std::string ue = prettyprint_ext_sym_set( current->get_ue_vars( ) );
                std::string killed = prettyprint_ext_sym_set( current->get_killed_vars( ) );
                std::string undef = prettyprint_ext_sym_set( current->get_undefined_behaviour_vars( ) );
                std::string reach_defs = prettyprint_reaching_definitions( current->get_reaching_definitions( ) );
                std::string subgr_liveness;
                if( _use_def_computed != '0' )
                    subgr_liveness = "LI: "         + live_in  + "\\n" +
                                        "KILL: "       + killed   + "\\n" +
                                        "UE: "         + ue       + "\\n" +
                                        "UNDEEF: "     + undef    + "\\n" +
                                        "LO: "         + live_out + "\\n" +
                                        "REACH DEFS: " + reach_defs;

                std::string task_deps = "";
                if( current->is_task_node( ) )
                {
                    task_deps = "\\n"
                                "input: "  + prettyprint_ext_sym_set( current->get_input_deps( ) ) + "\\n" +
                                "output: " + prettyprint_ext_sym_set( current->get_output_deps( ) ) + "\\n" +
                                "inout: "  + prettyprint_ext_sym_set( current->get_inout_deps( ) );
                }

                dot_graph += indent + "subgraph cluster" + ssgid.str( ) + "{\n";

                makeup_dot_block( subgraph_label );
                dot_graph += indent + "\tlabel=\"" + subgraph_label + "\";\n";
                subgraph_id++;

                std::vector<std::string> new_outer_edges;
                std::vector<Node*> new_outer_nodes;
                get_dot_subgraph(current, dot_graph, new_outer_edges, new_outer_nodes, indent, subgraph_id);
                std::stringstream ss; ss << current->get_id( );
                if( _use_def_computed != '0' && current->has_deps_computed( ) )
                    dot_graph += indent + "\t-" + ss.str( ) + "[label=\"" + subgr_liveness + task_deps + " \", shape=box]\n";
                else if( _use_def_computed != '0' )
                    dot_graph += indent + "\t-" + ss.str( ) + "[label=\"" + subgr_liveness + " \", shape=box]\n";
                dot_graph += indent + "}\n";

                for( std::vector<Node*>::iterator it = new_outer_nodes.begin( );
                        it != new_outer_nodes.end( );
                        ++it)
                {
                    std::vector<std::string> new_outer_edges_2;
                    std::vector<Node*> new_outer_nodes_2;
                    get_nodes_dot_data( *it, dot_graph, new_outer_edges_2, new_outer_nodes_2, indent, subgraph_id );
                }
                for( std::vector<std::string>::iterator it = new_outer_edges.begin( ); it != new_outer_edges.end( ); ++it )
                {
                    dot_graph += indent + ( *it );
                }
            }

            if( current->is_exit_node( ) )
            {   // Ending the graph traversal, either the master graph or any subgraph
                get_node_dot_data( current, dot_graph, indent );
            }
            else
            {
                bool must_print_following = true;
                std::stringstream sss;
                if( !current->is_graph_node( ) )
                {
                    if( (!current->has_key(_OUTER_NODE) ) ||
                        (current->has_key(_OUTER_NODE) &&
                            ( ( ! current->is_entry_node( ) && !current->get_entry_edges( ).empty( ) ) ||
                            current->is_entry_node( ) ) ) )
                    {
                        sss << current->get_id( );
                        get_node_dot_data( current, dot_graph, indent );
                    }
                    else
                    {
                        must_print_following = false;
                    }
                }
                else
                {
                    Node* exit_node = current->get_graph_exit_node( );
                    if( !current->get_entry_edges( ).empty( ) && !exit_node->get_entry_edges( ).empty( ) )
                    {
                        sss << exit_node->get_id( );
                        ObjectList<Edge*> exit_edges = current->get_exit_edges( );
                    }
                    else
                    {
                        must_print_following = false;
                    }
                }

                if( must_print_following )
                {
                    ObjectList<Edge*> exit_edges = current->get_exit_edges( );
                    for( ObjectList<Edge*>::iterator it = exit_edges.begin( ); it != exit_edges.end( ); ++it )
                    {
                        std::stringstream sst;
                        if( ( *it )->get_target( )->is_graph_node( ) )
                        {
                            sst << ( *it )->get_target( )->get_graph_entry_node( )->get_id( );
                        }
                        else
                        {
                            sst << ( *it )->get_target( )->get_id( );
                        }
                        std::string direction = "";
                        if( sss.str( ) == sst.str( ) )
                        {
                            direction = ", headport=n, tailport=s";
                        }

                        std::string extra_edge_attrs = "";
                        if( ( *it )->is_task_edge( ) )
                        {
                            extra_edge_attrs = ", style=dotted";
                        }

                        if( belongs_to_the_same_graph( *it ) )
                        {
                            dot_graph += indent + sss.str( ) + " -> " + sst.str( ) +
                                        " [label=\"" + ( *it )->get_label( ) + "\"" + direction + extra_edge_attrs + "];\n";
                            get_nodes_dot_data(( *it )->get_target( ), dot_graph,
                                            outer_edges, outer_nodes,
                                            indent, subgraph_id);
                        }
                        else
                        {
                            if( current->is_graph_node( ) )
                            {
                                get_node_dot_data(current, dot_graph, indent);
                            }
                            std::string mes = sss.str( ) + " -> " + sst.str( ) +
                                            " [label=\"" + ( *it )->get_label( ) + "\"" + direction + extra_edge_attrs + "];\n";
                            outer_edges.push_back( mes );
                            outer_nodes.push_back(( *it )->get_target( ) );
                        }
                    }
                }
            }
        }
    }

    void ExtensibleGraph::get_dot_subgraph( Node* current, std::string& dot_graph,
                                            std::vector<std::string>& outer_edges, std::vector<Node*>& outer_nodes,
                                            std::string indent, int& subgraph_id )
    {
        Node* entry_node = current->get_graph_entry_node( );
        get_nodes_dot_data( entry_node, dot_graph, outer_edges, outer_nodes, indent+"\t", subgraph_id );
    }

    void ExtensibleGraph::get_node_dot_data( Node* current, std::string& dot_graph, std::string indent )
    {
        std::string basic_block = "";
        std::stringstream ss; ss << current->get_id( );
        std::stringstream ss2;
        if( current->has_key( _OUTER_NODE ) )
            ss2 << current->get_outer_node( )->get_id( );
        else ss2 << "0";

        std::string basic_attrs = "margin=\"0.1,0.1, height=0.1, width=0.1\"";

        std::string live_in = prettyprint_ext_sym_set( current->get_live_in_vars( ) );
        std::string live_out = prettyprint_ext_sym_set( current->get_live_out_vars( ) );
        std::string ue = prettyprint_ext_sym_set( current->get_ue_vars( ) );
        std::string undef = prettyprint_ext_sym_set( current->get_undefined_behaviour_vars( ) );
        std::string killed = prettyprint_ext_sym_set( current->get_killed_vars( ) );
        std::string reach_defs = prettyprint_reaching_definitions(current->get_reaching_definitions( ) );
        std::string live_info;
        if( _use_def_computed != '0' )
            live_info = " | LI: "           + live_in +
                        " | KILL: "         + killed +
                        " | UE: "           + ue +
                        " | UNDEF: "        + undef +
                        " | LO: "           + live_out +
                        " | REACH DEFS: "   + reach_defs;

        switch( current->get_type( ) )
        {
            case ENTRY:
            {
                dot_graph += indent + ss.str( ) + "[label=\"" + ss.str( ) + " ENTRY \\n"
//                             + "REACH DEFS: " + prettyprint_reaching_definitions(current->get_reaching_definitions( ) )
                        + "\", shape=box, fillcolor=lightgray, style=filled];\n";
//                     dot_graph += indent + ss.str( ) + "[label=\" ENTRY\", shape=box, fillcolor=lightgray, style=filled, " + basic_attrs + "];\n";

                break;
            }
            case EXIT:
            {
                dot_graph += indent + ss.str( ) + "[label=\"" + ss.str( ) + " EXIT\", shape=box, fillcolor=lightgray, style=filled];\n";
//                     dot_graph += indent + ss.str( ) + "[label=\"EXIT\", shape=box, fillcolor=lightgray, style=filled, " + basic_attrs + "];\n";
                break;
            }
            case UNCLASSIFIED_NODE:
            {
//                     dot_graph += indent + ss.str( ) + "[label=\"" + ss.str( ) + " UNCLASSIFIED_NODE\"]\n";
                dot_graph += indent + ss.str( ) + "[label=\"UNCLASSIFIED_NODE\"]\n";
                break;
            }
            case OMP_BARRIER:
            {
                dot_graph += indent + ss.str( ) + "[label=\"BARRIER\", shape=diamond]\n";
                break;
            }
            case OMP_FLUSH:
            {
                dot_graph += indent + ss.str( ) + "[label=\"FLUSH\", shape=ellipse]\n";
                break;
            }
            case OMP_TASKWAIT:
            {
                dot_graph += indent + ss.str( ) + "[label=\"TASKWAIT\", shape=ellipse]\n";
                break;
            }
            case BREAK:
            {
                dot_graph += indent + ss.str( ) + "[label=\"BREAK\", shape=diamond]\n";
                break;
            }
            case CONTINUE:
            {
                dot_graph += indent + ss.str( ) + "[label=\"CONTINUE\", shape=diamond]\n";
                break;
            }
            case GOTO:
            case NORMAL:
            case LABELED:
            case FUNCTION_CALL:
            {
                // Get the Statements within the BB
                ObjectList<Nodecl::NodeclBase> node_block = current->get_statements( );
                std::string aux_str = "";
                for( ObjectList<Nodecl::NodeclBase>::iterator it = node_block.begin( ); it != node_block.end( ); it++ )
                {
                    if( it->is<Nodecl::ObjectInit>( ) )
                    {
                        Symbol it_s = it->as<Nodecl::ObjectInit>( ).get_symbol( );
                        aux_str = it_s.get_name( ) + " = " ;
                        aux_str += codegen_to_str( it_s.get_value( ).get_internal_nodecl( ),
                                                   nodecl_retrieve_context(it_s.get_value( ).get_internal_nodecl( ) ) );
                    }
                    else
                    {
                        aux_str = codegen_to_str(it->get_internal_nodecl( ),
                                                    nodecl_retrieve_context(it->get_internal_nodecl( ) ));
                    }
                    makeup_dot_block(aux_str);
                    basic_block += aux_str + "\\n";
                }
                basic_block = basic_block.substr( 0, basic_block.size( ) - 2 );   // Remove the last back space

                dot_graph += indent + ss.str( ) + "[label=\"{" + ss.str( ) + basic_block + live_info + "}\", shape=record, "
                            + basic_attrs + "];\n";

                break;
            }
            default:
                internal_error( "Undefined type of node '%s' founded while printing the graph.",
                                current->get_type_as_string( ).c_str( ) );
        };
    }

    static void makeup_dot_block( std::string& str )
    {
        int pos;
        // Escape double quotes
        pos = 0;
        while( ( pos=str.find( "\"", pos ) ) != -1 ) {
            str.replace ( pos, 1, "\\\"" );
            pos += 2;
        }
        // Delete implicit line feeds
        pos = 0;
        while( ( pos=str.find( "\n", pos ) ) != -1 ) {
            str.replace ( pos, 1, "" );
        }
        // Delete explicit line feeds
        pos = 0;
        while( ( pos=str.find( "\\n", pos ) ) != -1 ) {
            str.replace ( pos, 2, "\\\\n" );
            pos += 3;
        }
        // Escape the comparison symbols '<' and '>'
        pos = 0;
        while( ( pos=str.find( "<", pos ) ) != -1 ) {
            str.replace ( pos, 1, "\\<" );
            pos += 2;
        }
        pos = 0;
        while( ( pos=str.find( ">", pos ) ) != -1 ) {
            str.replace ( pos, 1, "\\>" );
            pos += 2;
        }
        // Escape the brackets '{' '}'
        pos = 0;
        while( ( pos=str.find( "{", pos ) ) != -1 ) {
            str.replace ( pos, 1, "\\{" );
            pos += 2;
        }
        pos = 0;
        while( ( pos=str.find( "}", pos ) ) != -1 ) {
            str.replace ( pos, 1, "\\}" );
            pos += 2;
        }
        // Escape the OR operand
        pos = 0;
        while( ( pos=str.find( "|", pos ) ) != -1 ) {
            str.replace ( pos, 1, "\\|" );
            pos += 2;
        }
        // Escape '%' operand
        pos = 0;
        while( ( pos=str.find( "%", pos ) ) != -1 ) {
            str.replace ( pos, 1, "\\%" );
            pos += 2;
        }
        // Escape '?' token
        pos = 0;
        while( ( pos=str.find( "?", pos ) ) != -1 ) {
            str.replace ( pos, 1, "\\?" );
            pos += 2;
        }
    }

    static std::string prettyprint_reaching_definitions( nodecl_map reach_defs )
    {
        std::string result;

        for( nodecl_map::iterator it = reach_defs.begin( ); it != reach_defs.end( ); ++it )
        {
            Nodecl::NodeclBase first = it->first, second = it->second;
            if( it->second.is_null( ) )
            {
                result += std::string( first.prettyprint( ) ) + " = UNKNOWN VALUE;@";
            }
            else
            {
                result += std::string( first.prettyprint( ) ) + " = "
                        + std::string( second.prettyprint( ) ) + ";@";
            }
        }

        makeup_dot_block(result);

        // We separate here in lines each reaching definition
        int pos = 0;
        while( ( pos=result.find( "@", pos ) ) != -1 ) {
            result.replace ( pos, 1, "\\n" );
            pos += 1;
        }

        return result;
    }

    static std::string prettyprint_ext_sym_set( Utils::ext_sym_set s)
    {
        std::string result;

        for( Utils::ext_sym_set::iterator it = s.begin( ); it != s.end( ); ++it )
        {
            if( it->get_nodecl( ).is_null( ) )
            {
                result += it->get_name( ) + ", ";
            }
            else
            {
                std::string nodecl_string( codegen_to_str( it->get_nodecl( ).get_internal_nodecl( ),
                                                           nodecl_retrieve_context( it->get_nodecl( ).get_internal_nodecl( ) ) ) );
                result += nodecl_string + ", ";
            }
        }

        result = result.substr( 0, result.size( ) - 2 );

        makeup_dot_block( result );

        return result;
    }
}
}