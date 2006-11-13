#include "tl-traverse.hpp"

namespace TL
{
	void DepthTraverse::add_predicate(Predicate<AST_t>& pred, TraverseFunctor& functor)
	{
		CondAction c(&pred, &functor);
		_pred_list.push_back(c);
	}

	void DepthTraverse::traverse(TL::AST_t node, ScopeLink scope_link)
	{
		TraverseFunctor no_op;
		TraverseFunctor* functor = &no_op;

		for (unsigned int i = 0; i < _pred_list.size(); i++)
		{
			Predicate<AST_t>* pred = _pred_list[i].first;

			if ((*pred)(node))
			{
				functor = _pred_list[i].second;
                break;
			}
		}

		AST ast = node._ast;

		Context ctx(scope_link);

		functor->preorder(ctx, node);

		for (int i = 0; i < ASTNumChildren(ast); i++)
		{
			AST child = ASTChild(ast, i);

			if (child != NULL)
			{
                AST_t w_child(child);
				traverse(w_child, scope_link);
			}
		}

		functor->postorder(ctx, node);
	}
}
