/*
    Acotes Translation Phase
    Copyright (C) 2007 - David Rodenas Pico <david.rodenas@bsc.es>
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
    
    $Id: tl-acotestransform.cpp 1611 2007-07-10 09:28:44Z drodenas $
*/
#include "tl-porttransform.h"


#include <assert.h>
#include <sstream>

#include "ac-peek.h"
#include "ac-port.h"
#include "ac-state.h"
#include "ac-task.h"
#include "ac-variable.h"
#include "tl-variabletransform.h"
#include "tl-transform.h"

namespace TL { namespace Acotes {
    
    
    
    /* ******************************************************
     * * Constructor
     * ******************************************************/
    
    PortTransform::PortTransform(const std::string& d) : driver(d) {
    }

    
    
    /* ******************************************************
     * * Auxiliary generators
     * ******************************************************/
    
    Source PortTransform::generatePort(Port* port)
    {
        assert(port);
        
        Source ss;

        if (port->isInput()) {
            ss << generateInputPort(port);
        } else if (port->isOutput()) {
            ss << generateOutputPort(port);
        } else {
            assert(0);
        }
        
        return ss;
    }
    
    Source PortTransform::generateBufferPort(Port* port)
    {
        assert(port);

        Source ss;

        if (port->isInput()) {
            ss << generateInputBufferPort(port);
        } else if (port->isOutput()) {
            ss << generateOutputBufferPort(port);
        } else {
            assert(0);
        }

        return ss;
    }

    Source PortTransform::generatePrevBufferWrite(Port* port)
    {
        assert(port);

        Source ss;

        if (port->isInput()) {
            //ss << generatePrevInputBufferPort(port);
            //ss << "inputprev();";
            ss << comment ("inputprev");
            ss << "";
        } else if (port->isOutput()) {
            ss << generatePrevOutputBufferPort(port);
        } else {
            assert(0);
        }

        return ss;
    }

    Source PortTransform::generateEndOfFile(Port* port)
    {
        assert(port);

        Source ss;

        if (port->isInput()) {
            ss << comment ("inputprev2");
        } else if (port->isOutput()) {
            ss << generateEndOfFilePort(port);
        } else {
            assert(0);
        }

        return ss;
    }

    Source PortTransform::generateNelemsBufferPort(Port* port)
    {
        assert(port);

        Source ss;

        if (port->isInput()) {
            ss << generateNelemsInputBufferPort(port);
        } else if (port->isOutput()) {
            ss << generateNelemsOutputBufferPort(port);
        } else {
            assert(0);
        }

        return ss;
    }

    Source PortTransform::generateCommitBufferPort(Port* port)
    {
        assert(port);
        Source ss;
        if (port->isOutput()) {
            ss << generateCommitOutputBufferPort(port);
        } else if (port->isInput()) {
            ss << generateCommitInputBufferPort(port);
        } else
            assert(0);

        return ss;
    }


    Source PortTransform::generate_endofstream_condition(Port* port)
    {
        assert(port);

        Source ss;

        if (port->isInput()) {
            ss << generate_eos_condition(port);
        } else if (port->isOutput()) {
            // noop
        } else {
            assert(0);
        }

        return ss;
    }

    Source PortTransform::generate_continue_condition(Port* port)
    {
        assert(port);

        Source ss;

        if (port->isInput()) {
            // noop
        } else if (port->isOutput()) {
            ss << generate_cont_condition(port);
        } else {
            assert(0);
        }

        return ss;
    }

    Source PortTransform::generateAcquire_task(Port* port)
    {
        assert(port);
        Source ss;
        Variable* variable= port->getVariable();
        //ss << "iii();";
        if (variable) {
           if (port->isOutput()) {
             printf ("AQUI2 control %d\n", port->isControl());
             //ss << "aaa();" ;
             //    << "__wbuf_" << variable->getName()
             //    << "_port" << port->getNumber() //<< "a()"
#ifdef ACOTES_DIRECT_BUFFER_ACCESS
             ss << "__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elem++;";
#else
             ss << "__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "["
               << "__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elem++"
               << "]"
               << " = " << variable->getName()
             //  //<< Transform::I(driver)->variable()->generateVariableName(variable)
               << ";"
               ;//AQUI2
#endif
             ss << "__out_store_" << variable->getName() << "_port"
                << port->getNumber() << "++;";
             ss << "if (__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elem"
               << " >= " << "__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elemno) __endofoutput = 1;" // HERE


               ;
           }
           else if (port->isInput()) {
             ss << "if (__rbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elem"
               << " >= " << "__rbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elemno) break;"
               ;

#ifdef ACOTES_DIRECT_BUFFER_ACCESS
             ss  << "__rbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elem++;";
#else
             ss  << variable->getName() << " = "
               << "__rbuf_" << variable->getName()
               << "_port" << port->getNumber() << "["
               << "__rbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elem++"
               << "]"
               << ";"
               ;//AQUI2
#endif
             ss << "__in_" << variable->getName() //<< "_port"
                //<< port->getNumber() 
                << "++;";
           }
           else assert(0);
        }
        return ss;
    }

    Source PortTransform::generateAcquire_task2(Port* port)
    {
        assert(port);
        Source ss;
        Variable* variable= port->getVariable();
        if (variable) {
           if (port->isOutput()) {
             ss << "if (__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elem"
               << " >= " << "__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elemno2) break"
               << ";"
               ;
           }
        }
        return ss;
    }

    Source PortTransform::generateAcquire(Port* port)
    {
        assert(port);
        
        Source ss;

#if 0        
        Variable* variable= port->getVariable();
        if (variable || port->isInput()) {
            if (port->isInput()) 
            { 
                ss << "iport_"; 
            }
            else if (port->isOutput()) 
            { 
                ss << "oport_"; 
            }
            else { assert(0); }
            
            ss  << "acquire"
                << "(" << port->getNumber() 
                << ", " << Transform::I(driver)->variable()->generateElementCount(variable)
                << ");";
        }

#else
        Variable* variable= port->getVariable();
        if (variable) {
           printf ("PortTransform::generateAcquire this one task %s\n", variable->getName().c_str());
           if (port->isOutput()) {
#ifdef ACOTES_DIRECT_BUFFER_ACCESS
             ss << "this_should_not_happen();";
#else
             ss << "__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "["
               << "__wbuf_" << variable->getName()
               << "_port" << port->getNumber() << "_elem"
               << "]"
               << " = " 
               << Transform::I(driver)->variable()->generateElementCount(variable)
               << ";"
               ;//AQUI
#endif
           }
        ss << "oport______acquite();";
        }
        ss << "";
#endif
        return ss;
    }
    
    Source PortTransform::generateInputPeek(Port* port)
    {
        assert(port);
        assert(port->isInput());

        Source ss;
        
        Variable* variable= port->getVariable();
        if (variable) {
            ss  << "{"
                << "  int acotescc__for_peek_index;"
                << "  for (acotescc__for_peek_index= 0"
                << "      ; acotescc__for_peek_index < " << Transform::I(driver)->variable()->generateElementCount(variable)
                << "      ; acotescc__for_peek_index++"
                << "      ) {"
                // for each element copies the value
                << "      memcpy"
                << "          ( &((" << Transform::I(driver)->variable()->generateReference(variable) << ")[acotescc__for_peek_index])"
                << "          , iport_peek"
                << "               (" << port->getNumber() 
                // if we have peek we need to read from the beggining
                << "               , " << port->getPeekWindow() << " + acotescc__for_peek_index"
                << "               )"
                // peeks the size of one element
                << "          , " << Transform::I(driver)->variable()->generateSizeof(variable)
                << "      );"
                << "  }"
                << "}";
        }
        
        return ss;
    }
    
    Source PortTransform::generateInputBufferAccess(Port* port)
    {
        assert(port);
        assert(port->isInput());

        Source ss;

        Variable* variable= port->getVariable();
        if (variable) {
            TL::Scope scope= variable->getSymbol().get_scope();

            ss  << "msf_local_buffer_handle_p h_"
                << "__rbuf_" << variable->getName()
                << "_port" << port->getNumber() << " = msf_get_current_read_buffer ("
                << port->getNumber() << ");";

#ifdef ACOTES_DIRECT_BUFFER_ACCESS
            ss  << variable->getName() << " = msf_get_buffer_address ("
                << "h_" << "__rbuf_" << variable->getName() 
                << "_port" << port->getNumber() << ");";
#else
            ss  << variable->getElementType().get_declaration(scope, "")
                << "  * __rbuf_" << variable->getName()
                << "_port" << port->getNumber() << " = msf_get_buffer_address ("
                << "h_" << "__rbuf_" << variable->getName() 
                << "_port" << port->getNumber() << ");";
#endif

            ss  << "unsigned int " << "__rbuf_" << variable->getName()
                << "_port" << port->getNumber()
                << "_elem = 0, "
                << "__rbuf_" << variable->getName()
                << "_port" << port->getNumber()
                << "_elemno = msf_get_elements_number(h_"
                << "__rbuf_" << variable->getName()
                << "_port" << port->getNumber() << ");";
            ss  << "__rbuf_" << variable->getName()
                << "_port" << port->getNumber()
                << "_elemno = (" << "__rbuf_" << variable->getName()
                << "_port" << port->getNumber() << "_elemno"
                << "<(1*1048576))?"
                << "__rbuf_" << variable->getName() 
                << "_port" << port->getNumber() << "_elemno"
                << ":(1*1048576);";
            ss  << "msf_get_next_read_buffer (" << port->getNumber()
                << ", __rbuf_" << variable->getName() 
                << "_port" << port->getNumber() << "_elemno + __in_"
                << variable->getName() << ");";

            ss  << "printf (\"task in elemno %d\\n\", __rbuf_"
                << variable->getName()
                << "_port" << port->getNumber() << "_elemno);";
            //ss  << "while (1)"; // moved to task
#if 0
            ss  << variable->getElementType().get_declaration(scope, "")
                << "  * __rbuf_" << variable->getName()
                << "_port" << port->getNumber() << " = msf_get_current_read_buffer ("
                << port->getNumber()                           // << ", 0, "
                //<< Transform::I(driver)->variable()->generateSizeof(variable)
                << ", __in_eload_" << variable->getName()
                << "_port" << port->getNumber() << ");"        //  , MSF_SYNC);"
                  ;
#endif
        }
      else
           fprintf (stderr, "Error: generating inputbufferaccess from control port with no variable associated\n");

        return ss;
    }
/* AQUI*/
    Source PortTransform::generateOutputBufferAccess(Port* port)
    {
        assert(port);
        assert(port->isOutput());
        Source ss;
        Source elem;

        Variable* variable= port->getVariable();
        if (variable) {
            TL::Scope scope= variable->getSymbol().get_scope();
            printf ("AQUI: PortTransform::generateOutputBufferAccess\n");
            
            //elem << "__wbuf_" << variable->getName()
            //     << "_port" << port->getNumber() << "_elemno";

            ss  << "msf_local_buffer_handle_p h_"
                << "__wbuf_" << variable->getName()
                << "_port" << port->getNumber() << " = msf_get_current_write_buffer ("
                << port->getNumber() << ", __out_store_"
                << variable->getName() << "_port" << port->getNumber() << ");";

#ifdef ACOTES_DIRECT_BUFFER_ACCESS
            ss  << variable->getName() << " = msf_get_buffer_address ("
                << "h_" << "__wbuf_" << variable->getName() 
                << "_port" << port->getNumber() << ");";
#else
            ss  << variable->getElementType().get_declaration(scope, "")
                << "  * __wbuf_" << variable->getName()
                << "_port" << port->getNumber() << " = msf_get_buffer_address ("
                << "h_" << "__wbuf_" << variable->getName() 
                << "_port" << port->getNumber() << ");";
#endif
            ss  << "unsigned int " << "__wbuf_" << variable->getName()
                << "_port" << port->getNumber()
                << "_elem = 0, "
                << "__wbuf_" << variable->getName()
                << "_port" << port->getNumber()
                << "_elemno = msf_get_elements_number(h_"
                << "__wbuf_" << variable->getName()
                << "_port" << port->getNumber() << ");";
            ss  << "__wbuf_" << variable->getName()
                << "_port" << port->getNumber()
                << "_elemno = (" << "__wbuf_" << variable->getName()
                << "_port" << port->getNumber() << "_elemno"
                << "<(1*1048576))?"
                << "__wbuf_" << variable->getName() 
                << "_port" << port->getNumber() << "_elemno"
                << ":(1*1048576);";
             ss << "printf (\"task out elemno %d\\n\", __wbuf_"
                << variable->getName()
                << "_port" << port->getNumber() << "_elemno);";


              //<< port->getNumber()                      // << ", 0, "
              ////<< Transform::I(driver)->variable()->generateSizeof(variable)
              //<< ", __out_eload_" << variable->getName()
              //<< "_port" << port->getNumber() << " + 1);" //, MSF_SYNC);"
                //;
          //ss  << variable->getName = *(
            // A for loop is necessary around the body
            // __ii = 0;
            // while (__ii < __n_eload_a_port0) {
            //      input variables
            //    variable->getName() = *(__wbuf_" << variable->getName()
            //     << "_port" << port->getNumber() );
            //     body...
            //      output variables
            //    *(__wbuf_" << variable->getName()
            //     << "_port" << port->getNumber() ) = variable->getName();
            // }
        }
      else
           fprintf (stderr, "Error: generating inputbufferaccess from control port with no variable associated\n");

        return ss;
    }

    Source PortTransform::generateOutputPeek(Port* port)
    {
        assert(port);
        assert(port->isOutput());

        Source ss;
//AQUI3
#if 1
        
        Variable* variable= port->getVariable();
        if (variable) {
            ss  << "{"
                << "  int acotescc__for_peek_index;"
                << "  for (acotescc__for_peek_index= 0"
                << "      ; acotescc__for_peek_index < " << Transform::I(driver)->variable()->generateElementCount(variable)
                << "      ; acotescc__for_peek_index++"
                << "      ) {"
                // for each element copies the value
                << "      memcpy"
                << "          ( oport_peek"
                << "               (" << port->getNumber() 
                << "               , acotescc__for_peek_index"
                << "               )"
                << "          , &((" << Transform::I(driver)->variable()->generateReference(variable) << ")[acotescc__for_peek_index])"
                // peeks the size of one element
                << "          , " << Transform::I(driver)->variable()->generateSizeof(variable)
                << "      );"
                << "  }"
                << "}";
        }
#else
                ss << "";
#endif
        
        return ss;
    }
    
    Source PortTransform::generatePop(Port* port)
    {
        assert(port);
        assert(port->isInput());
        
        Source ss;
        
        Variable* variable= port->getVariable();
        if (variable) {
            if (port->isInput()) 
            { 
                ss << "iport_"; 
            }
            else if (port->isOutput()) 
            { 
                ss << "oport_"; 
            }
            else { assert(0); }
            ss  << "pop"
                << "(" << port->getNumber() 
                << ", " << Transform::I(driver)->variable()->generateElementCount(variable)
                << ");";
        }
        
        return ss;
    }
    
    Source PortTransform::generatePush(Port* port)
    {
        assert(port);
        assert(port->isOutput());
        
        Source ss;

#if 0        
        Variable* variable= port->getVariable();
        if (variable || port->isOutput()) {
            if (port->isInput()) 
            { 
                ss << "iport_"; 
            }
            else if (port->isOutput()) 
            { 
                ss << "oport_"; 
            }
            else { assert(0); }
            ss  << "push"
                << "(" << port->getNumber() 
                << ", " << Transform::I(driver)->variable()->generateElementCount(variable)
                << ");";
        }
#else
	ss << "";
#endif
        
        return ss;
    }

    
    Source PortTransform::generateInputPort(Port* port) {
        assert(port);
        assert(port->isInput());
        
        Source ss;
        
        Variable* variable= port->getVariable();
//        ss << "task_iport"
//                << "( " << port->getTask()->getName()
//                << ", " << port->getNumber()
//                ;
//        if (port->hasVariable()) {
//            ss  << ", " << Transform::I(driver)->variable()->generateSizeof(variable)
//                << ", " << Transform::I(driver)->variable()->generateElementCount(variable)
//                << ", " << port->getPeekWindow() << "+" << Transform::I(driver)->variable()->generateElementCount(variable)
//                ;
//        } else {
//            ss  << ", 0, 1, 0";
//        }

      if (port->getTask()->isImplicitTask())
        ss << "";
      else {
        if (variable) {
	   ss << "msf_set_task_global_buffer_size ("
              << port->getTask()->getName() << ", " << port->getNumber();
           ss << ", acotes__bs[acotes__tg][" << port->getTask()->getNum() 
              << "][" << port->getNumber() << "][0]";
           //ss << ", 32768";
           //ss  << ", " << Transform::I(driver)->variable()->generateSizeof(variable);
           ss << ");";
        }
        else
           // ss << ", 1";   // was 0...
           ss << "";

        if (variable) {
           ss << "msf_set_task_local_buffer_size ("
              << port->getTask()->getName() << ", " << port->getNumber();
           ss << ", acotes__bs[acotes__tg][" << port->getTask()->getNum() 
              << "][" << port->getNumber() << "][1]";
           //ss  << ", " << Transform::I(driver)->variable()->generateSizeof(variable);
           ss << ");";
        }
        else
           //ss << ", 1";   // was 0...
           ss << "";

        //ss << "msf_set_task_runtime(" << 
      }
//        if (port->hasPeek()) {
//            Peek* peek= port->getPeek();
//            ss  << ", " << Transform::I(driver)->variable()->generateReference(peek->getHistory()->getVariable())
//                << ", " << port->getPeekWindow()
//                ;
//        } else {
//            ss  << ", (void*) 0, 0";
//        }
//        ss      << ");";
        
        if (port->isReplicate()) {
            ss << "iport_replicate"
                    << "( " << port->getTask()->getName()
                    << ", " << port->getNumber()
                    << ");";
        }
        
        return ss;
    }

    Source PortTransform::generate_eos_condition(Port* port) {
        assert(port);
        assert(port->isInput());

        Source ss;

        Variable* variable= port->getVariable();
        if (port->hasVariable()) {
           ss << "( __in_" << variable->getName() << " < __in_elems_to_process_"
              << variable->getName() << ")"
             ;
        }
        else {
           //ss << "( __in_ctrl_" << port->getNumber() << " < "
           //   << "__in_elems_to_process_ctrl_" << port->getNumber() << ")"
           ss << "1" ;
        }
        return ss;
    }

    Source PortTransform::generate_cont_condition(Port* port) {
        assert(port);
        assert(port->isOutput());

        Source ss;

        Variable* variable= port->getVariable();
        if (port->hasVariable()) {
           ss << "( __out_store_" << variable->getName() 
              << "_port" << port->getNumber() << " < __out_elems_to_process_"
              << variable->getName() << ")"
             ;
        }
        else {
           //ss << "( __in_ctrl_" << port->getNumber() << " < "
           //   << "__in_elems_to_process_ctrl_" << port->getNumber() << ")"
           ss << "1" ;
        }
        return ss;
    }


    Source PortTransform::generateNelemsInputBufferPort(Port* port) {
        assert(port);
        assert(port->isInput());

        Source ss;

   //port->getTask()->getName()

        Variable* variable= port->getVariable();
        if (port->hasVariable()) {
           ss << "int __in_" << variable->getName()
              << " = 0, __in_elems_to_process_"
              << variable->getName() << " = " << "msf_get_max_elem_to_process("
              << port->getNumber() << ");"
                ; 
           ss << "printf (\"Task in elems %d\\n\", __in_elems_to_process_"
              << variable->getName() << ");";
           //ss << "int __in_eload_" << variable->getName()
           //   << "_port" << port->getNumber() << " = "
          //    << "msf_get_elements_number("
          //    << port->getNumber()
          //    << ");"
          //      ;
        }
        else {
           //ss << "int __in_ctrl_" << port->getNumber()
           //   << " = 0, __in_elems_to_process_ctrl_"
           //   << port->getNumber() << " = " << "msf_get_max_elem_to_process("
           //   << port->getNumber() << ");"
           //     ;
           //ss << "int __in_eload_ctrl_"
           //   << "_port" << port->getNumber() << " = "
           //   << "msf_get_elements_number("
           //   << port->getNumber()
           //   << ");"
           //     ;
           ss << "" ;
        }

        return ss;
    }

    Source PortTransform::generateCommitOutputBufferPort(Port* port) {
        assert(port);
        assert(port->isOutput());
        Source ss;

        Variable* variable= port->getVariable();
        if (port->hasVariable()) {
           ss << "msf_commit_written_data(" << port->getNumber() << ", "
              << "__out_store_" << variable->getName() 
              << "_port" << port->getNumber() << ", "
              << "__transfer_type);";
           ss << "printf (\"msf_commit_written_data (" 
              << port->getNumber() << ", %d, %d)\\n\", __out_store_" 
              << variable->getName()
              << "_port" << port->getNumber() << ", " << "__transfer_type);";
              
        }
        else {
           ss << "";
           printf ("This should not happen!!!\n");
           assert(0);
        }

        return ss;
    }

    Source PortTransform::generateCommitInputBufferPort(Port* port) {
        assert(port);
        assert(port->isInput());
        Source ss;

        Variable* variable= port->getVariable();
        if (port->hasVariable()) {
           ss << comment ("MSF_BUFFER_PORT_ACTIVE");
           ss << "msf_free_read_data(" << port->getNumber() << ", "
              << "__in_" << variable->getName() 
              //<< "_port" << port->getNumber() 
              << ", "
              << "0);";
              //<< "__transfer_type);";
        }
        else {
           ss << "";
           printf ("This should not happen!!!\n");
           //assert(0);
        }

        return ss;
    }

    Source PortTransform::generatePrevOutputBufferPort(Port * port) {
        assert (port);
        assert(port->isOutput());

        Source ss;

        if (port->hasVariable()) {
           ss << "msf_send_previous_write_buffer (" << port->getNumber() << ");";
        }
        else
           ss << "";

        return ss;
    }

    Source PortTransform::generateEndOfFilePort(Port * port) {
        assert (port);
        assert(port->isOutput());

        Source ss;

        if (port->hasVariable()) {
           Variable * v = port->getVariable();
           ss << "if (__wbuf_" << v->getName() 
              << "_port" << port->getNumber() << "_elem < __wbuf_" 
              << v->getName() << "_port" << port->getNumber() << "_elemno) {"
              << comment ("MSF_BUFFER_PORT_LAST")
              << " __transfer_type = 1; /* MSF_BUFFER_PORT_LAST */"
              << "break;"
              << "}"
              ;
        }
        else
           ss << "";

        return ss;
    }



    Source PortTransform::generateNelemsOutputBufferPort(Port* port) {
        assert(port);
        assert(port->isOutput());

        Source ss;

   //port->getTask()->getName()

        Variable* variable= port->getVariable();
        if (port->hasVariable()) {
           ss << "int __out_" << variable->getName()
              << " = 0, __out_elems_to_process_"
              << variable->getName() << " = " << "msf_get_max_elem_to_process("
              << port->getNumber() << ");"
                ;
           ss << "printf (\"Task out elems %d\\n\", __out_elems_to_process_"
              << variable->getName() << ");";
           ss << "int __out_store_" << variable->getName()
              << "_port" << port->getNumber() << " = 0;"
                ;
           //ss << "int __out_eload_" << variable->getName()
           //   << "_port" << port->getNumber() << " = "
           //   << "msf_get_elements_number("
           //   << port->getNumber()
           //   << ");"
           //     ;
        }
        else {
           //ss << "int __out_ctrl_" << port->getNumber()
            //  << " = 0, __out_elems_to_process_ctrl_"
            //  << port->getNumber() << " = " << "msf_get_max_elem_to_process("
            //  << port->getNumber() << ");"
            //    ;
           //ss << "int __out_eload_ctrl_"
           //   << "_port" << port->getNumber() << " = "
           //   << "msf_get_elements_number("
           //   << port->getNumber()
           //   << ");"
           //     ;
           ss << "" ;
        }

        return ss;
    }

    Source PortTransform::generateInputBufferPort(Port* port) {
        assert(port);
        assert(port->isInput());

        Source ss;

   //port->getTask()->getName()

        Variable* variable= port->getVariable();
        if (port->hasVariable()) {
           ss << comment ("MSF_IN_BUFFER_PORT");
           ss << "msf_add_buffer_port (2 /*MSF_IN_BUFFER_PORT*/, "
                << Transform::I(driver)->variable()->generateSizeof(variable)
                << ", " << port->getNumber()
                << ", \"__" << variable->getName() << "__\");"
                ;
        }
        else {
           //ss << "msf_add_buffer_port (2 /*MSF_IN_BUFFER_PORT*/, "
           //     << "0"
           //     << ", " << port->getNumber()
           //     << ", 0);";
           ss << "";
        }
        return ss;
    }

    Source PortTransform::generateOutputBufferPort(Port* port) {
        assert(port);
        assert(port->isOutput());

        Source ss;

   //port->getTask()->getName()
        Variable* variable= port->getVariable();
        if (port->hasVariable()) {
           ss << comment ("MSF_OUT_BUFFER_PORT");
           ss << "msf_add_buffer_port (3 /*MSF_OUT_BUFFER_PORT*/, "
                << Transform::I(driver)->variable()->generateSizeof(variable)
                << ", " << port->getNumber()
                << ", \"__" << variable->getName() << "__\");"
                ;
      }
      else {
         ss << comment ("MSF_OUT_BUFFER_PORT");
         ss << "msf_add_buffer_port (3 /*MSF_OUT_BUFFER_PORT*/, "
              << "0"
              << ", " << port->getNumber()
              << ", 0);";
      }


        return ss;
    }

    
    Source PortTransform::generateOutputPort(Port* port) {
        assert(port);
        assert(port->isOutput());
        
        Source ss;
        
        Variable* variable= port->getVariable();
//        ss << "task_oport"
//                << "( " << port->getTask()->getName()
//                << ", " << port->getNumber()
//                ;
//        if (variable) {
//            ss  << ", " << Transform::I(driver)->variable()->generateSizeof(variable)
//                << ", " << Transform::I(driver)->variable()->generateElementCount(variable)
//                << ", " << Transform::I(driver)->variable()->generateElementCount(variable)
//                ;
//        } else {
//            ss  << ", 0, 1, 0";
//        }
    if (port->getTask()->isImplicitTask())
      ss << "";
    else {
      if (variable) {
         ss << "msf_set_task_global_buffer_size ("
            << port->getTask()->getName() << ", " << port->getNumber();
         ss << ", acotes__bs[acotes__tg][" << port->getTask()->getNum() 
            << "][" << port->getNumber() << "][0]";
         //ss << ", 32768";
         //ss << ", " << Transform::I(driver)->variable()->generateSizeof(variable);
         ss      << ");";
      }
      else
          //ss << ", 0";
          ss << "";

      if (variable) {
         ss << "msf_set_task_local_buffer_size ("
            << port->getTask()->getName() << ", " << port->getNumber();
         ss << ", acotes__bs[acotes__tg][" << port->getTask()->getNum() 
            << "][" << port->getNumber() << "][1]";
         //ss << ", " << Transform::I(driver)->variable()->generateSizeof(variable);
         ss     << ");";
      }
      else
          //ss << ", 0";
         ss << "";
    }
        
        return ss;
    }
    
    
} /* end namespace Acotes */ } /* end namespace TL */
    
    