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

#include "cxx-codegen.h"
#include "tl-edge.hpp"
#include "tl-node.hpp"

namespace TL {
namespace Analysis {

    Edge::Edge( Node *source, Node *target, bool is_task_edge_, Edge_type type, std::string label )
        : _source( source ), _target( target )
    {
        set_data( _EDGE_TYPE, type );
        set_data( _EDGE_LABEL, label );
        set_data( _IS_TASK_EDGE, is_task_edge_ );
    }

    Node* Edge::get_source( ) const
    {
        return _source;
    }

    Node* Edge::get_target( ) const
    {
        return _target;
    }

    Edge_type Edge::get_type( )
    {
        if( has_key( _EDGE_TYPE ) )
        {
            return get_data<Edge_type>( _EDGE_TYPE );
        }
        else
        {
            return __UnclassifiedEdge;
        }
    }

    //! Returns a string with the edge type
    inline std::string edge_type_to_str( Edge_type et )
    {
        switch( et )
        {
            #undef EDGE_TYPE
            #define EDGE_TYPE(X) case __##X : return #X;
            EDGE_TYPE_LIST
            #undef EDGE_TYPE
            default: WARNING_MESSAGE( "Unexpected type of edge '%d'", et );
        }
        return "";
    }
    
    std::string Edge::get_type_as_string( )
    {
        std::string result = "";

        if ( has_key( _EDGE_TYPE ) )
        {
            Edge_type etype = get_data<Edge_type>( _EDGE_TYPE );
            result = edge_type_to_str( etype );
        }

        return result;
    }

    bool Edge::is_task_edge( )
    {
        if ( has_key( _IS_TASK_EDGE ) )
        {
            return get_data<bool>( _IS_TASK_EDGE );
        }
        else
        {
            internal_error( "Edge between '%d' and '%d 'without attribute _IS_TASK. This attribute is mandatory for all edges",
                            _source->get_id( ), _target->get_id( ) );
        }
    }

    std::string Edge::get_label( )
    {
        std::string label = "";

        if ( has_key( _EDGE_TYPE) &&
             get_data<Edge_type>( _EDGE_TYPE ) != __UnclassifiedEdge )
        {
            Edge_type etype = get_data<Edge_type>( _EDGE_TYPE );
            switch ( etype )
            {
                case __Always:
                case __Case:
                case __Catch:       label = get_data<std::string>( _EDGE_LABEL );
                                    break;
                case __FalseEdge:   label = "FALSE";
                                    break;
                case __GotoEdge:    label = get_data<std::string>( _EDGE_LABEL );
                                    break;
                case __TrueEdge:    label = "TRUE";
                                    break;
                default:            WARNING_MESSAGE( "Unexpected type '%d'\n", etype );
            };
        }

        return label;
    }

    void Edge::set_label( std::string label )
    {
        std::string new_label = "";
        if( get_data<std::string>( _EDGE_LABEL ) != "")
        {
            new_label = get_data<std::string>( _EDGE_LABEL ) + ", ";
        }
        new_label += label;
        set_data( _EDGE_LABEL, new_label );
    }

    void Edge::set_true_edge( )
    {
        set_data( _EDGE_TYPE, __TrueEdge );
    }

    void Edge::set_false_edge( )
    {
        set_data( _EDGE_TYPE, __FalseEdge );
    }

    void Edge::set_catch_edge( )
    {
        set_data( _EDGE_TYPE, __Catch );
    }

    bool Edge::is_always_edge( )
    {
        return ( get_data<Edge_type>(_EDGE_TYPE) == __Always );
    }

    bool Edge::is_case_edge( )
    {
        return ( get_data<Edge_type>(_EDGE_TYPE) == __Case );
    }

    bool Edge::is_catch_edge( )
    {
        return ( get_data<Edge_type>(_EDGE_TYPE) == __Catch );
    }

    bool Edge::is_false_edge( )
    {
        return ( get_data<Edge_type>(_EDGE_TYPE) == __FalseEdge );
    }

    bool Edge::is_goto_edge( )
    {
        return ( get_data<Edge_type>(_EDGE_TYPE) == __GotoEdge );
    }

    bool Edge::is_true_edge( )
    {
        return ( get_data<Edge_type>(_EDGE_TYPE) == __TrueEdge );
    }


    // ****************************************************************************** //
    // **************** Getters and setters for constants analysis ****************** //

    void Edge::set_executable( bool value )
    {
        set_data( _IS_EXECUTABLE, value );
    }

    bool Edge::is_executable( )
    {
        if ( has_key( _IS_EXECUTABLE ) )
        {
            return get_data<bool>( _IS_EXECUTABLE );
        }
        else
        {
            internal_error( "Requesting execution information in edge '%d->%d', \
                            which does not contain this info", _source->get_id( ), _target->get_id( ) );
        }
    }

    // ************** END getters and setters for constants analysis **************** //
    // ****************************************************************************** //
}
}
