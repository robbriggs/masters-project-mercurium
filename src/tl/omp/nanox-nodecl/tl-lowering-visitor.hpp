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

#include "tl-nanox-nodecl.hpp"
#include "tl-nodecl-visitor.hpp"
#include "tl-outline-info.hpp"
#include "tl-nodecl-utils.hpp"
#include "tl-omp-core.hpp" 

#include <set>
#include <stdio.h>

namespace TL { namespace Nanox {

class LoweringVisitor : public Nodecl::ExhaustiveVisitor<void>
{
    public:
        LoweringVisitor(Lowering*, RefPtr<OpenMP::FunctionTaskSet> function_task_set);
        ~LoweringVisitor();

        virtual void visit(const Nodecl::FunctionCode& function_code);
        virtual void visit(const Nodecl::OpenMP::Atomic& construct);
        virtual void visit(const Nodecl::OpenMP::BarrierFull& construct);
        virtual void visit(const Nodecl::OpenMP::Critical& construct);
        virtual void visit(const Nodecl::OpenMP::FlushMemory& construct);
        virtual void visit(const Nodecl::OpenMP::For& construct);
        virtual void visit(const Nodecl::OpenMP::Master& construct);
        virtual void visit(const Nodecl::OpenMP::Parallel& construct);
        virtual void visit(const Nodecl::OpenMP::Sections& construct);
        virtual void visit(const Nodecl::OpenMP::Single& construct);
        virtual void visit(const Nodecl::OpenMP::Workshare& construct);
        virtual void visit(const Nodecl::OpenMP::TargetDeclaration& construct);
        virtual void visit(const Nodecl::OpenMP::Task& construct);
        virtual void visit(const Nodecl::OpenMP::TaskCall& construct);
        virtual void visit(const Nodecl::OpenMP::TaskExpression& task_expr);
        virtual void visit(const Nodecl::OpenMP::TaskwaitShallow& construct);
        virtual void visit(const Nodecl::OpenMP::WaitOnDependences& construct);

    private:

        Lowering* _lowering;
        RefPtr<OpenMP::FunctionTaskSet> _function_task_set;

        // this map is used to avoid repeating the definitions of the structure
        // 'nanos_const_wd_definition_t'
        std::map<int, Symbol> _declared_const_wd_type_map;

        TL::Symbol declare_argument_structure(OutlineInfo& outline_info, Nodecl::NodeclBase construct);
        bool c_type_needs_vla_handling(TL::Type t);

        void emit_async_common(
                Nodecl::NodeclBase construct,
                TL::Symbol function_symbol,
                TL::Symbol called_task,
                Nodecl::NodeclBase statements,
                Nodecl::NodeclBase priority_expr,
                Nodecl::NodeclBase if_condition,
                Nodecl::NodeclBase final_condition,
                Nodecl::NodeclBase task_label,
                bool is_untied,
                bool storeir,
                OutlineInfo& outline_info,
                OutlineInfo* parameter_outline_info,
                Nodecl::NodeclBase* placeholder_task_expr_transformation);

        void handle_vla_entity(OutlineDataItem& data_item, OutlineInfo& outline_info);
        void handle_vla_type_rec(TL::Type t, OutlineInfo& outline_info,
            OutlineDataItem& outline_data_item);
        void handle_vla_saved_expr(Nodecl::NodeclBase saved_expr, OutlineInfo& outline_info);

        void fill_arguments(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                Source& fill_outline_arguments,
                Source& fill_immediate_arguments
                );

        int count_dependences(OutlineInfo& outline_info);
        int count_copies(OutlineInfo& outline_info);
        int count_copies_dimensions(OutlineInfo& outline_info);

        void fill_copies(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                OutlineInfo* parameter_outline_info,
                TL::Symbol structure_symbol,
                // Source arguments_accessor,
                // out
                int &num_copies,
                Source& copy_ol_decl,
                Source& copy_ol_arg,
                Source& copy_ol_setup,
                Source& copy_imm_arg,
                Source& copy_imm_setup,
                Symbol& xlate_function_symbol);

        void fill_copies_nonregion(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                int num_copies,
                // Source arguments_accessor,
                // out
                Source& copy_ol_decl,
                Source& copy_ol_arg,
                Source& copy_ol_setup,
                Source& copy_imm_arg,
                Source& copy_imm_setup);
        void fill_copies_region(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                int num_copies,
                int num_copies_dimensions,
                // Source arguments_accessor,
                // out
                Source& copy_ol_decl,
                Source& copy_ol_arg,
                Source& copy_ol_setup,
                Source& copy_imm_arg,
                Source& copy_imm_setup);

        void emit_translation_function_nonregion(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                OutlineInfo* parameter_outline_info,
                TL::Symbol structure_symbol,
                bool allow_multiple_copies,
                TL::Symbol& xlate_function_symbol);

        void emit_translation_function_region(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                OutlineInfo* parameter_outline_info,
                TL::Symbol structure_symbol,
                TL::Symbol& xlate_function_symbol);

        void fill_dependences_internal(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                Source arguments_accessor,
                bool on_wait,
                // out
                Source& result_src
                );

        void handle_dependency_item(
                Nodecl::NodeclBase ctr,
                TL::DataReference dep_expr,
                OutlineDataItem::DependencyDirectionality dir,
                int current_dep_num,
                Source& dependency_regions,
                Source& dependency_init,
                Source& result_src);

        void fill_dependences(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                Source arguments_accessor,
                // out
                Source& result_src
                );

        void fill_dependences_taskwait(
                Nodecl::NodeclBase ctr,
                OutlineInfo& outline_info,
                // out
                Source& result_src
                );

        void check_pendant_writes_on_subexpressions(
                OutlineDataItem::TaskwaitOnNode* c,
                // out
                TL::Source& code);

        void generate_mandatory_taskwaits(
                OutlineInfo& outline_info,
                // out
                TL::Source& taskwait_on_after_wd_creation_opt);

        void emit_wait_async(Nodecl::NodeclBase construct,
                bool has_dependences,
                OutlineInfo& outline_info,
                bool is_noflush);

        static void fill_dimensions(int n_dims, int actual_dim, int current_dep_num,
                Nodecl::NodeclBase dep_expr,
                Nodecl::NodeclBase * dim_sizes, 
                Type dep_type, 
                Source& dims_description, 
                Source& dependency_regions_code, 
                Scope sc);

        Source fill_const_wd_info(
                Source &struct_arg_type_name,
                bool is_untied,
                bool mandatory_creation,
                bool is_function_task,
                const std::string& wd_description,
                OutlineInfo& outline_info,
                Nodecl::NodeclBase construct);

        TL::Symbol declare_const_wd_type(
                int num_devices,
                Nodecl::NodeclBase construct);

        void allocate_immediate_structure(
                OutlineInfo& outline_info,
                Source &struct_arg_type_name,
                Source &struct_size,

                // out
                Source &immediate_decl,
                Source &dynamic_size);

        void parallel_spawn(
                OutlineInfo& outline_info,
                Nodecl::NodeclBase construct,
                Nodecl::NodeclBase num_replicas,
                Nodecl::NodeclBase if_condition,
                const std::string& outline_name,
                TL::Symbol structure_symbol);

        Source get_loop_distribution_source_worksharing(
                const Nodecl::OpenMP::For &construct,
                Nodecl::List& distribute_environment,
                Nodecl::RangeLoopControl& range,
                OutlineInfo& outline_info,
                TL::Symbol slicer_descriptor,
                Nodecl::NodeclBase &placeholder1,
                Nodecl::NodeclBase &placeholder2,
                Nodecl::NodeclBase &reduction_initialization,
                Nodecl::NodeclBase &reduction_code);
        void distribute_loop_with_outline_worksharing(
                const Nodecl::OpenMP::For& construct,
                Nodecl::List& distribute_environment,
                Nodecl::RangeLoopControl& range,
                OutlineInfo& outline_info,
                Nodecl::NodeclBase& statements,
                TL::Symbol slicer_descriptor,
                Source &outline_distribute_loop_source,
                // Loop (in the outline distributed code)
                Nodecl::NodeclBase& outline_placeholder1,
                // Auxiliar loop (when the step is not known at compile time, in the outline distributed code)
                Nodecl::NodeclBase& outline_placeholder2,
                Nodecl::NodeclBase& reduction_initialization,
                Nodecl::NodeclBase& reduction_code);
        void lower_for_worksharing(const Nodecl::OpenMP::For& construct);
        void loop_spawn_worksharing(
                OutlineInfo& outline_info,
                Nodecl::NodeclBase construct,
                Nodecl::List distribute_environment,
                Nodecl::RangeLoopControl& range,
                const std::string& outline_name,
                TL::Symbol structure_symbol,
                TL::Symbol slicer_descriptor);

        Source get_loop_distribution_source_slicer(
                const Nodecl::OpenMP::For &construct,
                Nodecl::List& distribute_environment,
                Nodecl::RangeLoopControl& range,
                OutlineInfo& outline_info,
                TL::Symbol slicer_descriptor,
                Nodecl::NodeclBase &placeholder1,
                Nodecl::NodeclBase &placeholder2,
                Nodecl::NodeclBase &reduction_initialization,
                Nodecl::NodeclBase &reduction_code);
        void distribute_loop_with_outline_slicer(
                const Nodecl::OpenMP::For& construct,
                Nodecl::List& distribute_environment,
                Nodecl::RangeLoopControl& range,
                OutlineInfo& outline_info,
                Nodecl::NodeclBase& statements,
                TL::Symbol slicer_descriptor,
                Source &outline_distribute_loop_source,
                // Loop (in the outline distributed code)
                Nodecl::NodeclBase& outline_placeholder1,
                // Auxiliar loop (when the step is not known at compile time, in the outline distributed code)
                Nodecl::NodeclBase& outline_placeholder2,
                Nodecl::NodeclBase& reduction_initialization,
                Nodecl::NodeclBase& reduction_code);
        void lower_for_slicer(const Nodecl::OpenMP::For& construct);
        void loop_spawn_slicer(
                OutlineInfo& outline_info,
                Nodecl::NodeclBase construct,
                Nodecl::List distribute_environment,
                Nodecl::RangeLoopControl& range,
                const std::string& outline_name,
                TL::Symbol structure_symbol,
                TL::Symbol slicer_descriptor);

        static bool there_are_reductions(OutlineInfo& outline_info);

        Source full_barrier_source();

        void reduction_initialization_code(
                OutlineInfo& outline_info,
                Nodecl::NodeclBase ref_tree,
                Nodecl::NodeclBase construct);
        void reduction_initialization_code_slicer(
                OutlineInfo& outline_info,
                Nodecl::NodeclBase ref_tree,
                Nodecl::NodeclBase construct);

        std::set<std::string> _lock_names;

        void perform_partial_reduction(OutlineInfo& outline_info, Nodecl::NodeclBase ref_tree);
        void perform_partial_reduction_slicer(OutlineInfo& outline_info, Nodecl::NodeclBase ref_tree,
                Nodecl::Utils::SimpleSymbolMap*& symbol_map);

        Nodecl::NodeclBase emit_critical_region(
                const std::string lock_name,
                Nodecl::NodeclBase construct,
                Nodecl::NodeclBase statements);

        Source emit_allocate_statement(TL::Symbol sym, 
                int &lower_bound_index, int &upper_bound_index);

        Source update_lastprivates(OutlineInfo& outline_info, const std::string& loop_descriptor_name);

        Symbol get_function_ptr_of(TL::Symbol sym, TL::Scope original_scope);
        Symbol get_function_ptr_of(TL::Type t, TL::Scope original_scope);
        Symbol get_function_ptr_of_impl(TL::Symbol sym, TL::Type t, TL::Scope original_scope);

        void add_field(OutlineDataItem& outline_data_item, 
                TL::Type new_class_type,
                TL::Scope class_scope,
                TL::Symbol new_class_symbol,
                Nodecl::NodeclBase construct);

        static Nodecl::NodeclBase get_size_for_dimension(
                TL::Type array_type,
                int fortran_dimension,
                DataReference data_reference);

        static Nodecl::NodeclBase get_lower_bound(Nodecl::NodeclBase dep_expr, int dimension_num);
        static Nodecl::NodeclBase get_upper_bound(Nodecl::NodeclBase dep_expr, int dimension_num);

        void visit_task(
                const Nodecl::OpenMP::Task& construct,
                bool inside_task_expression,
                Nodecl::NodeclBase* placeholder_task_expr_transformation);

        void visit_task_call(
                const Nodecl::OpenMP::TaskCall& construct,
                bool inside_task_expression,
                Nodecl::NodeclBase* placeholder_task_expr_transformation);

        void visit_task_call_c(
                const Nodecl::OpenMP::TaskCall& construct,
                bool inside_task_expression,
                Nodecl::NodeclBase* placeholder_task_expr_transformation);

        void visit_task_call_fortran(
                const Nodecl::OpenMP::TaskCall& construct,
                bool inside_task_expression,
                Nodecl::NodeclBase* placeholder_task_expr_transformation);

        void remove_fun_tasks_from_source_as_possible(const OutlineInfo::implementation_table_t& implementation_table);

        typedef std::map<OpenMP::Reduction*, TL::Symbol> reduction_map_t;
        reduction_map_t _basic_reduction_map_openmp;
        reduction_map_t _vector_reduction_map_openmp;

        reduction_map_t _reduction_map_ompss;
        void create_reduction_function(OpenMP::Reduction* red,
                Nodecl::NodeclBase construct,
                TL::Type reduction_type,
                TL::Symbol& basic_reduction_function,
                TL::Symbol& vector_reduction_function);
        TL::Symbol create_basic_reduction_function_c(OpenMP::Reduction* red, Nodecl::NodeclBase construct);
        TL::Symbol create_basic_reduction_function_fortran(OpenMP::Reduction* red, Nodecl::NodeclBase construct);

        TL::Symbol create_reduction_function_slicer(OutlineDataItem* red, Nodecl::NodeclBase construct);
        TL::Symbol create_reduction_function_fortran_slicer(OutlineDataItem* ol, Nodecl::NodeclBase construct);

        TL::Symbol create_vector_reduction_function_c(OpenMP::Reduction* red, Nodecl::NodeclBase construct);

        reduction_map_t _reduction_cleanup_map;
        TL::Symbol create_reduction_cleanup_function(OpenMP::Reduction* red, Nodecl::NodeclBase construct);

        Nodecl::NodeclBase fill_adapter_function(
                TL::Symbol adapter_function,
                TL::Symbol called_function,
                Nodecl::Utils::SimpleSymbolMap* &symbol_map,
                Nodecl::NodeclBase original_function_call,
                Nodecl::NodeclBase original_environment,
                TL::ObjectList<TL::Symbol> &save_expressions,
                bool inside_task_expression,
                // out
                Nodecl::NodeclBase& task_construct,
                Nodecl::NodeclBase& statements_of_task_seq,
                Nodecl::NodeclBase& new_environment);
};

} }
