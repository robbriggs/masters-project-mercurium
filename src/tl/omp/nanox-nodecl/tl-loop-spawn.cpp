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


#include "tl-source.hpp"
#include "tl-lowering-visitor.hpp"
#include "tl-nodecl-utils.hpp"

#include "tl-predicateutils.hpp"

namespace TL { namespace Nanox {

    void LoweringVisitor::loop_spawn(OutlineInfo& outline_info,
            Nodecl::NodeclBase construct,
            Nodecl::List distribute_environment,
            Nodecl::List ranges,
            const std::string& outline_name,
            TL::Symbol structure_symbol)
    {
        if (ranges.size() != 1)
        {
            internal_error("Only ranges of 1 dimension implemented", 0);
        }

        Nodecl::OpenMP::Schedule schedule = distribute_environment.find_first<Nodecl::OpenMP::Schedule>();
        ERROR_CONDITION(schedule.is_null(), "Schedule tree is missing", 0);

        Nodecl::OpenMP::ForRange distribute_range = ranges[0].as<Nodecl::OpenMP::ForRange>();
        Nodecl::NodeclBase lower = distribute_range.get_lower();
        Nodecl::NodeclBase upper = distribute_range.get_upper();
        Nodecl::NodeclBase step = distribute_range.get_step();

        Source struct_size;
        Source dynamic_size;
        Source struct_arg_type_name = structure_symbol.get_name();
        struct_size << "sizeof( " << struct_arg_type_name << " )" << dynamic_size;

        Source immediate_decl;
        allocate_immediate_structure(
                outline_info,
                struct_arg_type_name,
                struct_size,
                // out
                immediate_decl,
                dynamic_size);

        Nodecl::NodeclBase fill_outline_arguments_tree;
        Source fill_outline_arguments;

        Nodecl::NodeclBase fill_immediate_arguments_tree;
        Source fill_immediate_arguments;

        Source call_outline_function;

        Source schedule_setup;

        if (schedule.get_text() == "runtime")
        {
            schedule_setup
                <<     "omp_sched_t nanos_runtime_sched;"
                <<     "err = nanos_omp_get_schedule(&nanos_runtime_sched, &nanos_chunk);"
                <<     "if (err != NANOS_OK)"
                <<         "nanos_handle_error(err);"
                <<     "nanos_ws_t current_ws_policy = nanos_omp_find_worksharing(nanos_runtime_sched);"
                ;
        }
        else
        {
            schedule_setup
                <<     "nanos_ws_t current_ws_policy = nanos_omp_find_worksharing(omp_sched_" << schedule.get_text() << ");"
                <<     "if (current_ws_policy == 0)"
                <<         "nanos_handle_error(NANOS_UNIMPLEMENTED);"
                ;
        }

        schedule_setup
            <<     "int nanos_chunk;"
            <<     "nanos_chunk = " << as_expression(schedule.get_chunk()) << ";"
            ;

        Source worksharing_creation;
        worksharing_creation
            <<     "err = nanos_worksharing_create(&wsd, current_ws_policy, (void**)&nanos_setup_info_loop, &single_guard);"
            <<     "if (err != NANOS_OK)"
            <<         "nanos_handle_error(err);"
            ;

        Source const_wd_info;
        const_wd_info
            << fill_const_wd_info(struct_arg_type_name,
                    outline_name,
                    /* is_untied */ false,
                    /* mandatory_creation */ true);

        Source spawn_code;
        spawn_code
        << "{"
        <<     as_type(get_bool_type()) << " single_guard;"
        <<     "nanos_err_t err;"
        <<     schedule_setup
        <<     "nanos_ws_info_loop_t nanos_setup_info_loop;"
        <<     "nanos_setup_info_loop.lower_bound = " << as_expression(lower) << ";"
        <<     "nanos_setup_info_loop.upper_bound = " << as_expression(upper) << ";"
        <<     "nanos_setup_info_loop.loop_step = "   << as_expression(step)  << ";"
        <<     "nanos_setup_info_loop.chunk_size = nanos_chunk;"
        <<     "nanos_ws_desc_t *wsd;"
        <<     worksharing_creation
        <<     "if (single_guard)"
        <<     "{"
        <<         "int sup_threads;"
        <<         "err = nanos_team_get_num_supporting_threads(&sup_threads);"
        <<         "if (err != NANOS_OK)"
        <<             "nanos_handle_error(err);"
        <<         "if (sup_threads > 0)"
        <<         "{"
        <<             "err = nanos_malloc((void**)&(wsd->threads), sizeof(nanos_thread_t) * sup_threads, \"\", 0);"
        <<             "if (err != NANOS_OK)"
        <<                 "nanos_handle_error(err);"
        <<             "err = nanos_team_get_supporting_threads(&wsd->nths, wsd->threads);"
        <<             "if (err != NANOS_OK)"
        <<                 "nanos_handle_error(err);"
        <<             struct_arg_type_name << " *ol_args = (" << struct_arg_type_name <<"*) 0;"
        <<             const_wd_info
        <<             "nanos_wd_t wd = (nanos_wd_t) 0;"
        <<             "nanos_wd_dyn_props_t dyn_props;"
        <<             "dyn_props.tie_to = (nanos_thread_t)0;"
        <<             "dyn_props.priority = 0;"

        <<             "static nanos_slicer_t replicate = (nanos_slicer_t)0;"
        <<             "if (replicate == (nanos_slicer_t)0)"
        <<                 "replicate = nanos_find_slicer(\"replicate\");"
        <<             "if (replicate == (nanos_slicer_t)0)"
        <<                 "nanos_handle_error(NANOS_UNIMPLEMENTED);"
        <<             "err = nanos_create_sliced_wd(&wd, "
        <<                                           "nanos_wd_const_data.base.num_devices, nanos_wd_const_data.devices, "
        <<                                           "(size_t)" << struct_size << ",  nanos_wd_const_data.base.data_alignment, "
        <<                                           "(void**)&ol_args, nanos_current_wd(), replicate,"
        <<                                           "&nanos_wd_const_data.base.props, &dyn_props, 0, (nanos_copy_data_t**)0);"
        <<             "if (err != NANOS_OK)"
        <<                 "nanos_handle_error(err);"
        <<             "ol_args->wsd = wsd;"
        <<             statement_placeholder(fill_outline_arguments_tree)
        <<             "err = nanos_submit(wd, 0, (nanos_dependence_t *) 0, (nanos_team_t) 0);"
        <<             "if (err != NANOS_OK)"
        <<                 "nanos_handle_error(err);"
        <<             "err = nanos_free(wsd->threads);"
        <<             "if (err != NANOS_OK)"
        <<                 "nanos_handle_error(err);"
        <<         "}"
        <<     "}"
        <<     immediate_decl
        <<     "imm_args.wsd = wsd;"
        <<     statement_placeholder(fill_immediate_arguments_tree)
        <<     outline_name << "(imm_args);"
        << "}"
        ;

        fill_arguments(construct, outline_info, fill_outline_arguments, fill_immediate_arguments);

        FORTRAN_LANGUAGE()
        {
            // Parse in C
            Source::source_language = SourceLanguage::C;
        }
        Nodecl::NodeclBase spawn_code_tree = spawn_code.parse_statement(construct);
        FORTRAN_LANGUAGE()
        {
            Source::source_language = SourceLanguage::Current;
        }

        if (!fill_outline_arguments.empty())
        {
            Nodecl::NodeclBase new_tree = fill_outline_arguments.parse_statement(fill_outline_arguments_tree);
            fill_outline_arguments_tree.integrate(new_tree);
        }

        if (!fill_immediate_arguments.empty())
        {
            Nodecl::NodeclBase new_tree = fill_immediate_arguments.parse_statement(fill_immediate_arguments_tree);
            fill_immediate_arguments_tree.integrate(new_tree);
        }

        construct.integrate(spawn_code_tree);
    }

} }
