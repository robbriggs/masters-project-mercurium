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

#include "codegen-phase.hpp"
#include "tl-builtin.hpp"

#include "clang/CodeGen/CodeGenAction.h"
#include "clang/Driver/Compilation.h"
#include "clang/Driver/Driver.h"
#include "clang/Driver/Tool.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/DiagnosticOptions.h"
#include "clang/Frontend/FrontendDiagnostic.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"
#include "clang/AST/ASTContext.h"
#include "clang/Serialization/ASTWriter.h"

#include "llvm/Module.h"
#include "llvm/Config/config.h"
#include "llvm/ADT/OwningPtr.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Config/config.h"
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Bitcode/BitstreamWriter.h"
#include "llvm/Instructions.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Bitcode/ReaderWriter.h"

#include "llvm/Analysis/Verifier.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/PassManager.h"
#include "llvm/Support/IRReader.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/ValueSymbolTable.h"

#include "llvm/Transforms/IPO/InlinerPass.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <stdio.h>
#include <string.h>
#include <fstream>
#include <iomanip>
#include <iostream>

#include "tl-source.hpp"
#include "tl-counters.hpp"
#include "tl-nodecl-utils.hpp"
//#include "tl-outline-info.hpp"
#include "tl-replace.hpp"
#include "tl-compilerpipeline.hpp"

#include "tl-nodecl-utils-c.hpp"
#include "tl-nodecl-utils-fortran.hpp"
#include "tl-symbol-utils.hpp"

#include "codegen-phase.hpp"
#include "codegen-fortran.hpp"

#include "cxx-cexpr.h"
#include "cxx-profile.h"
#include "cxx-driver-utils.h"
#include "cxx-symbol-deep-copy.h"

using namespace clang;
using namespace clang::driver;

#define contloop(type, value, contence) \
  for (type::iterator it = value.begin(), E = value.end(); it != E; it++) { \
    contence ;\
  }

#define contprint(type, value) contloop(type, value, std::cout<<*it<<"\n")

template <class T>
void print_container(T &v)
{
  for (typename T::iterator it = v.begin(),
    E = v.end();
    it != E;
    it++)
  {
    std::cout << *it << ",";
  }
  std::cout << "\n";
}

llvm::sys::Path GetExecutablePath(const char *Argv0) {
  // This just needs to be some symbol in the binary; C++ doesn't
  // allow taking the address of ::main however.
  void *MainAddr = (void*) (intptr_t) GetExecutablePath;
  return llvm::sys::Path::GetMainExecutable(Argv0, MainAddr);
}

static void stream_bc_in_c(llvm::Module *Module, std::string &symbol, std::ofstream &file)
{
  std::string str;
  llvm::raw_string_ostream str_stream(str); 
  llvm::WriteBitcodeToFile(Module, str_stream);
  str_stream.str();
  
  file << "const char _binary_" << symbol << "_start[] = {";
  std::string::iterator it = str.begin(), E = str.end();
  E--;
  for (; it != E; ++it)
  {
    file << "0x" << std::hex << std::setw(2) << std::setfill('0') << static_cast<unsigned int>(static_cast<unsigned char>(*it)) << ", ";
  }

  file << "0x" << std::hex << std::setw(2) << std::setfill('0') << static_cast<unsigned int>(static_cast<unsigned char>(*it)) << "};";
  //file << "\nconst unsigned int _binary_" << symbol << "_size = " << std::dec << str.size() << ";";
  file << "\nconst int _binary_" << symbol << "_size = " << std::dec << str.size() << ";";
}

static llvm::Module *gen_llvm_module(std::string &filename, std::vector<std::string> *func_list)
{
  std::cout << "Looking for " << filename << "\n";
   void *MainAddr = (void*) (intptr_t) GetExecutablePath;
   llvm::sys::Path Path = GetExecutablePath(compilation_process.argv[0]);
   TextDiagnosticPrinter *DiagClient = new TextDiagnosticPrinter(llvm::errs(), DiagnosticOptions());

   llvm::IntrusiveRefCntPtr<DiagnosticIDs> DiagID(new DiagnosticIDs());
   DiagnosticsEngine Diags(DiagID, DiagClient);
   Driver TheDriver(Path.str(), llvm::sys::getHostTriple(),
                   "a.out", /*IsProduction=*/false, Diags);
   TheDriver.setTitle("clang interpreter");

   // FIXME: This is a hack to try to force the driver to do something we can
  // recognize. We need to extend the driver library to support this use model
  // (basically, exactly one input, and the operation mode is hard wired).

  llvm::SmallVector<const char *, 16> Args;
  Args.push_back(compilation_process.argv[0]);
  Args.push_back(filename.c_str());
  Args.push_back("-I/usr/lib/gcc/x86_64-redhat-linux/4.4.4/include/"); // Fails without
  Args.push_back("-fsyntax-only");
  for (llvm::SmallVector<const char *, 16>::iterator it = Args.begin(), E = Args.end(); it != E; it++) {
    std::cout << *it << "\n" ;
  }
  llvm::OwningPtr<Compilation> C(TheDriver.BuildCompilation(Args));
  if (!C)
    return NULL;
  std::cout << "Made compiler\n";

  // FIXME: This is copied from ASTUnit.cpp; simplify and eliminate.

  // We expect to get back exactly one command job, if we didn't something
  // failed. Extract that job from the compilation.
  const driver::JobList &Jobs = C->getJobs();
  std::cout << "Number of jobs " << Jobs.size() << "\n";
  if (Jobs.size() != 1 || !isa<driver::Command>(*Jobs.begin())) {
    llvm::SmallString<256> Msg;
    llvm::raw_svector_ostream OS(Msg);
    C->PrintJob(OS, C->getJobs(), "; ", true);
    Diags.Report(diag::err_fe_expected_compiler_job) << OS.str();
    return NULL;
  }

  std::cout << "Made job list\n";

  const driver::Command *Cmd = cast<driver::Command>(*Jobs.begin());
  if (llvm::StringRef(Cmd->getCreator().getName()) != "clang") {
    Diags.Report(diag::err_fe_expected_clang_command);
    return NULL;
  }

  std::cout << "Made command\n";

  // Initialize a compiler invocation object from the clang (-cc1) arguments.
  const driver::ArgStringList &CCArgs = Cmd->getArguments();
  llvm::OwningPtr<CompilerInvocation> CI(new CompilerInvocation);
  CompilerInvocation::CreateFromArgs(*CI,
                                     const_cast<const char **>(CCArgs.data()),
                                     const_cast<const char **>(CCArgs.data()) +
                                       CCArgs.size(),
                                     Diags);

  std::cout << "Made invocation\n";

  // Show the invocation, with -v.
  if (CI->getHeaderSearchOpts().Verbose) {
    llvm::errs() << "clang invocation:\n";
    C->PrintJob(llvm::errs(), C->getJobs(), "\n", true);
    llvm::errs() << "\n";
  }

  // Create a compiler instance to handle the actual work.
  CompilerInstance Clang;
  Clang.setInvocation(CI.take());

  std::cout << "Made Clang\n";

  // Create the compilers actual diagnostics engine.
  Clang.createDiagnostics(int(CCArgs.size()),const_cast<char**>(CCArgs.data()));
  if (!Clang.hasDiagnostics())
    return NULL;

  std::cout << "Made Diagnostics\n";


  // Infer the builtin include path if unspecified.
  if (Clang.getHeaderSearchOpts().UseBuiltinIncludes &&
      Clang.getHeaderSearchOpts().ResourceDir.empty())
    Clang.getHeaderSearchOpts().ResourceDir =
      CompilerInvocation::GetResourcesPath(compilation_process.argv[0], MainAddr);

  std::cout << "Ifnered \n";

  // Create and execute the frontend to generate an LLVM bitcode module.
  llvm::OwningPtr<CodeGenAction> Act(new EmitLLVMOnlyAction());
  if (!Clang.ExecuteAction(*Act))
    return NULL;

  std::cout << "Made Action\n";

  Clang.createASTContext();
  ASTContext& ast = Clang.getASTContext();

  std::cout << "Got context\n";

  llvm::Module *Module = Act->takeModule();

  std::cout << "takeModule\n";

  std::ofstream file;
  std::string binary_filename = filename + ".binary.c";
  file.open (binary_filename.c_str());

  for (std::vector<std::string>::iterator it = func_list->begin(), E = func_list->end(); it != E; it++)
  {
    stream_bc_in_c(Module, *it, file);
  }

  CURRENT_CONFIGURATION->source_language = SOURCE_LANGUAGE_C;

  compilation_configuration_t* configuration = ::get_compilation_configuration("auxcc");
   ERROR_CONDITION (configuration == NULL, "auxcc is needed.", 0);

  // Make sure phases are loaded (this is needed for codegen)
  load_compiler_phases(configuration);

  TL::CompilationProcess::add_file(binary_filename, "auxcc");
  ::mark_file_for_cleanup(binary_filename.c_str());
  return Module;
}


namespace Codegen
{
    void CodegenPhase::run(TL::DTO& dto)
    {
        TL::File output_file = dto["output_file"];
        FILE* f = output_file.get_file();

        Nodecl::NodeclBase n = dto["nodecl"];

        this->codegen_top_level(n, f);

        if (compilation_process.current_compilation_configuration->functions_to_generate_ir_for != NULL)
        {
          std::cout << "WOOP WOOP\n";
          std::vector<std::string> *func_list = static_cast<std::vector<std::string> *>(CURRENT_CONFIGURATION->functions_to_generate_ir_for);
          std::string file_name(func_list->at(0) + ".c");

          // Get code
          FILE *pFile = fopen (file_name.c_str() , "w");
          this->codegen_top_level(n, pFile);
          fclose (pFile);

          gen_llvm_module(file_name, func_list);

          // Clean up
          compilation_process.current_compilation_configuration->functions_to_generate_ir_for = NULL;
        }
    }
    void CodegenPhase::handle_parameter(int n, void* data)
    {}
}

Codegen::CodegenPhase& Codegen::get_current()
{
    CodegenPhase* result = reinterpret_cast<CodegenPhase*>(CURRENT_CONFIGURATION->codegen_phase);

    return *result;
}
