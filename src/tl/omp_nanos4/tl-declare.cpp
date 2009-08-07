#include "tl-omptransform.hpp"

namespace TL
{
    namespace Nanos4
    {
        void OpenMPTransform::declare_reduction_postorder(PragmaCustomConstruct ctr)
        {
            // Do nothing but remove the directive
            ctr.get_ast().remove_in_list();
        }
    }
}