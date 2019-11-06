/*++
Copyright (c) 2019

Module Name:

    aeval_cmds.cpp

Abstract:
    Synth-Lib commands for SMT2 front-end.

Author:

    ---

Notes:

--*/
#include "aeval/aeval_cmds.h"
#include "cmd_context/cmd_context.h"

#include "ast/ast_pp.h"

#include "cmd_context/parametric_cmd.h"
#include "muz/base/fp_params.hpp"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/scoped_timer.h"
#include "util/trail.h"

#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include <ast/rewriter/th_rewriter.h>
#include "muz/spacer/spacer_util.h"

#include <iomanip>
#include <iostream>
#include <set>



#define DEBUG true

namespace aeval {

namespace {

    struct smt_utils {
        cmd_context& m_cmd;
        ast_manager& m;
        arith_util m_arith;
        params_ref m_params;
        ref<solver> m_solver;

        smt_utils(cmd_context& cmd_ctx, ast_manager& m)
            : m_cmd(cmd_ctx)
            , m(m)
            , m_arith(m)
        {
        }
        bool implies(expr* a, expr* b)
        {
            return !is_sat(a, m.mk_not(b));
        }
        bool is_equil(expr* a, expr* b)
        {
            return implies(a, b) && implies(b, a);
        }
        bool is_sat(expr* e)
        {
            m_solver = m_cmd.get_solver_factory()(m, m_params, false, true, false, symbol::null);
            m_solver->push();
            m_solver->assert_expr(e);
            lbool r = m_solver->check_sat();
            m_solver->pop(1);
            return r == lbool::l_true;
        }

        bool is_sat(expr* e1, expr* e2)
        {
            m_solver = m_cmd.get_solver_factory()(m, m_params, false, true, false, symbol::null);
            m_solver->push();
            m_solver->assert_expr(e1);
            m_solver->assert_expr(e2);
            lbool r = m_solver->check_sat();
            m_solver->pop(2);
            return r == lbool::l_true;
        }

        /**
     * Return "e + eps"
     */
        expr_ref plus_eps(expr* e, bool isInt)
        {
            //if (m_arith.is_is_int(e) && isInt)
            // return m_arith.mk_int(m_arith);

            if (isInt)
                return expr_ref(m_arith.mk_add(e, m_arith.mk_int(1)), m);
            else
                return expr_ref(m_arith.mk_add(e, m_arith.mk_real(1)), m);
        }
        /**
     * Return "e - eps"
     */
        expr_ref minus_eps(expr* e, bool isInt)
        {
            //if (m_arith.is_is_int(e) && isInt)
            // return m_arith.mk_int(m_arith);

            if (isInt)
                return expr_ref(m_arith.mk_sub(e, m_arith.mk_int(1)), m);
            else
                return expr_ref(m_arith.mk_sub(e, m_arith.mk_real(1)), m);
        }
        expr_ref mover(expr* e, func_decl* var)
        {
            expr_ref r(m);
            proof_ref pr(m);

            th_rewriter s(m, m_params);
            th_solver solver(m_cmd);
            s.set_solver(alloc(th_solver, m_cmd));
            s(e, r, pr);

            /**
         *  Transform the inequalities by the following rules:
         *  (a + .. + var + .. + b <= c ) -> (var <= -1*a + .. + -1*b + c)
         *  (a + .. + -1*var + .. + b <= c) -> (-1*var <= -1*a + .. + -1*b + c )
         *  (a <= b + .. + var + .. + c) -> (-1*var <= (-1)*a + b + .. + c)
         *  (a <= b + .. + (-1)*var + .. + c) -> (var <= (-1)*a + b + .. + c)
         *
         *  same for >=
         */
            if (is_app(r) && is_cmp(r)) {

                app* a = to_app(r);
                expr* left = a->get_arg(0);

                if (is_desired_term(left, var))
                    return r;

                expr* right = a->get_arg(1);
                expr_ref excluded_term(m);
                expr_ref res = exclude_var_from_add(right, var, excluded_term);
                //app * a2 = to_app(res);

                expr_ref new_right(m_arith.mk_add(res, m_arith.mk_uminus(left)), m);

                expr_ref new_left_simplified(m);
                s(m_arith.mk_uminus(excluded_term), new_left_simplified);

                //if (DEBUG)
                //   std::cout << "new_right: " << mk_ismt2_pp(new_right, m, 3) << "\n";

                if (m.is_eq(r))
                    r = m.mk_eq(new_left_simplified, new_right);

                else if (m_arith.is_gt(r))
                    r = m_arith.mk_gt(new_left_simplified, new_right);
                else if (m_arith.is_ge(r))
                    r = m_arith.mk_ge(new_left_simplified, new_right);
                else if (m_arith.is_lt(r))
                    r = m_arith.mk_lt(new_left_simplified, new_right);
                else if (m_arith.is_le(r))
                    r = m_arith.mk_le(new_left_simplified, new_right);
            }
            return r;
        }
        /** expression e has a view:
        * (+ a b c (* 2 d) e ...)
    */
        expr_ref exclude_var_from_add(expr* e, func_decl* var, expr_ref& term_out)
        {
            if (m_arith.is_add(e)) {
                app* a = to_app(e);
                expr_ref_vector args_stack(m);
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    expr* arg = a->get_arg(i);
                    if (m_arith.is_add(arg)) {
                        // TODO
                        //std::cerr<< "mover_for_add: not yet implemented for the addition into a addition" << std::endl;
                        args_stack.push_back(exclude_var_from_add(arg, var, term_out));
                    } else if (is_desired_term(arg, var)) {
                        if (i == 0)
                            return expr_ref(e, m);
                        else {
                            term_out = arg;
                            continue;
                        }
                    } else {
                        args_stack.push_back(arg);
                    }
                }
                expr* new_add = m_arith.mk_add(args_stack.size(), args_stack.c_ptr());
                return expr_ref(new_add, m);
            } else if (is_desired_term(e, var)) {
                term_out = e;
                return expr_ref(m_arith.mk_int(0), m);
            }
            return expr_ref(e, m);
        }
        /** expression e has a view:
        * c*var or var
    */
        bool is_desired_term(expr* e, func_decl* var)
        {
            if (is_app(e)) {
                app* a = to_app(e);
                if (m_arith.is_mul(e)) {
                    expr* arg = a->get_arg(1);
                    return is_desired_term(arg, var);
                } else {
                    //expr * arg = a->get_arg(0);
                    return a->get_decl() == var;
                }
            }
            return false;
        }
        /**
     *  Trivial simplifier:
     *  (-1*a <= -1*b) -> (a >= b)
     *  (-1*a >= -1*b) -> (a <= b)
     *  (-1*a == -1*b) -> (a == b)
     */
        expr_ref ineq_reverter(expr* e)
        {
            expr_ref r(e, m);
            app* a = to_app(e);
            if (a->get_num_args() != 2)
                return r;
            if (!is_negation_var(a->get_arg(0)))
                return r;
            expr_ref new_left = additive_inverse(a->get_arg(0));
            expr_ref new_right = additive_inverse(a->get_arg(1));
            if (m.is_eq(e)) {
                r = m.mk_eq(new_left, new_right);
            } else if (m_arith.is_lt(e)) {
                r = m_arith.mk_gt(new_left, new_right);
            } else if (m_arith.is_le(e))
                r = m_arith.mk_ge(new_left, new_right);
            else if (m_arith.is_gt(e))
                r = m_arith.mk_lt(new_left, new_right);
            else if (m_arith.is_ge(e))
                r = m_arith.mk_le(new_left, new_right);
            return r;
        }
        bool is_negation_var(expr* e)
        {
            if (m_arith.is_uminus(e))
                return true;
            else {
                return (m_arith.is_mul(e) && m.are_equal(to_app(e)->get_arg(0), m_arith.mk_int(-1)));
            };
        }
        expr_ref additive_inverse(expr* e)
        {
            if (m_arith.is_uminus(e))
                return expr_ref(to_app(e)->get_arg(0), m);
            return expr_ref(m_arith.mk_uminus(e), m);
        }
        bool is_cmp(expr* e)
        {
            return m_arith.is_lt(e) || m_arith.is_le(e) || m_arith.is_gt(e) || m_arith.is_ge(e) || m.is_eq(e);
        }

        expr_ref con_join(expr_ref_vector& vec)
        {
            expr_ref all(m);
            if (vec.size() > 1)
                all = m.mk_and(vec.size(), vec.c_ptr());
            else {
                all = vec[0].get();
            }
            return all;
        }
    };

    class aevall_solver {
        typedef obj_hashtable<expr> expr_set;
        typedef obj_map<func_decl, expr*> decl2expr_map;
        typedef obj_map<func_decl, expr_ref_vector> decl2expr_ref_vec;
        //obj_map<expr, expr_set*> m_hypmap;
    private:
        cmd_context& m_cmd;
        ast_manager& m;
        ref<solver> m_solver;
        expr_ref_vector m_projections;

        expr_ref_vector m_subst_vec;

        unsigned m_partitioning_size;
        smt_utils m_utils;
        arith_util m_arith;
        func_decl_ref_vector m_sensitive_vars;
        expr_ref m_constraints;
        expr_ref m_skol_scope;
        vector<decl2expr_map> m_subst;
        vector<decl2expr_map> m_eval;
        //decl2expr_ref_vec       m_skolem_constraints;
        unsigned m_fresh_var_ind;

    public:
        aevall_solver(cmd_context& cmd_ctx, ast_manager& m, solver* solver)
            : m_cmd(cmd_ctx)
            , m(m)
            , m_solver(solver)
            , m_projections(m)
            , m_subst_vec(m)
            , m_partitioning_size(0)
            , m_utils(cmd_ctx, m)
            , m_arith(m)
            , m_sensitive_vars(m)
            , m_constraints(m)
            , m_skol_scope(m)

        {
        }

        bool solve(func_decl_ref_vector& exist_vars, expr_ref constraints)
        {
            //[+] reset
            m_subst.reset();
            m_eval.reset();

            //[-] reset
            m_constraints = constraints;

            bool res = true;
            m_solver->push();
            m_solver->assert_expr(constraints);

            while (m_solver->check_sat() == lbool::l_true) {
                model_ref model;
                m_solver->get_model(model);
                if (DEBUG) {
                    std::cout << "model: " << *model << std::endl;
                }
                get_MBP_and_skolem(model, exist_vars, constraints);
                m_solver->pop(1);
                m_solver->assert_expr(m.mk_not(m_projections.back()));
                if (m_solver->check_sat() == lbool::l_false) {
                    res = false;
                    break;
                } else {
                    // keep a model in case the formula is invalid
                    //m = smt.getModel();
                    // for (auto &e: sVars)
                    //  modelInvalid[e] = m.eval(e);
                }
                m_solver->push();
                m_solver->assert_expr(constraints);
            }
            get_scolem_functions(exist_vars);
            return res;
        }

        void get_MBP_and_skolem(model_ref model, func_decl_ref_vector& exist_vars, expr* e)
        {
            decl2expr_map subst_map, eval_map;
            expr_ref result(e, m);
            for (auto var = exist_vars.begin(); var != exist_vars.end();) {
                //Z3_qe_model_project_skolem

                app_ref_vector vars(m);
                auto var_app = m.mk_const(*var);
                vars.push_back(var_app);

                //result = to_expr (body);
                expr_map emap(m);

                spacer::qe_project(m, vars, result, model, emap);

                get_local_skolems(model, *var, emap, result, subst_map, eval_map);
                var++;
                /*ExprMap map;
          pr = z3_qe_model_project_skolem (z3, m, *exp, pr, map);
          if (skol) getLocalSkolems(m, *exp, map, substsMap, modelMap, pr);
          Expr var = *exp;
          tmpVars.erase(exp++);*/
            }
            if (DEBUG) {
                std::cout << "\t mbp: " << mk_ismt2_pp(result, m, 3) << std::endl;
                ;
                // outs() << "\nkolMaps " << skolMaps << "\n";
            }
            m_projections.push_back(result.get());
            m_eval.push_back(eval_map);
            m_subst.push_back(subst_map);
            m_partitioning_size++;
        }

        void get_local_skolems(model_ref model, func_decl* var, expr_map& map, expr* mbp, decl2expr_map& subst_map, decl2expr_map& eval_map)
        {
            expr_set substs;
            for (auto& e : map)
                fillSubsts(&e.get_key(), e.get_value(), mbp, substs);
            if (substs.size() == 0) {
                if (DEBUG)
                    std::cout << "WARNING: subst is empty for " << var->get_name() << "\n";
            } else {
                auto it = substs.begin();
                expr* conjoin = *it;
                it++;
                while (it != substs.end()) {

                    conjoin = m.mk_and(conjoin, *it);
                    it++;
                }

                if (DEBUG)
                    std::cout << "subst_map: " << mk_ismt2_pp(conjoin, m, 3) << "\n";
                m_subst_vec.push_back(conjoin);
                subst_map.insert(var, expr_ref(conjoin, m));
            }
            expr_ref res_eval(m);
            model->eval(var, res_eval);
            if (DEBUG)
                std::cout << "eval: " << res_eval << std::endl;
            eval_map.insert(var, expr_ref(m.mk_eq(m.mk_const(var), res_eval), m));
            /*   if (m.eval(exp) != exp){
            modelMap[exp] = mk<EQ>(exp, m.eval(exp));
            }*/
        }
        void fillSubsts(expr* ef, expr* es, expr* mbp, expr_set& substs)
        {
            if (DEBUG)
                std::cout << "fillSubsts " << mk_ismt2_pp(ef, m, 3) << " :: " << mk_ismt2_pp(es, m, 3) << " in " << mk_ismt2_pp(mbp, m, 3) << "\n";
            if (m.is_true(es) || m_utils.implies(mbp, es)) {
                substs.insert(ineqNegReverter(ef));
            } else if (!sameBoolOrCmp(ef, es)) {
                std::cout << "WARNING!! sameBoolOrCmp" << std::endl;
                //substs.insert(m.mk_eq(ineqNegReverter(ef), ineqNegReverter(es)));
            }
            /*(else if (isOpX<FALSE>(es))
            {
              // useless (just for optim)
            }
            else if (isOpX<TRUE>(es) || u.implies(mbp, es))
            {
              substs.insert(ineqNegReverter(ef));
            }*/
        }

        expr_ref get_scolem_functions(func_decl_ref_vector& exist_vars)
        {
            /*  m_skolem_constraints.reset();
        //[+] initialize // TODO optimize memory
        for (auto & a : exist_vars)
        {
          expr_ref_vector t(m);
          for (unsigned i = 0; i < m_partitioning_size; i++)
          {
            t.push_back(m_subst[i][a]); // should be on i-th position
          }
            m_skolem_constraints.insert(a, t);
        }
        //[-] initialize*/

            m_skol_scope = m.mk_true();
            m_sensitive_vars.reset();
            for (func_decl* a : exist_vars) {
                m_sensitive_vars.push_back(a);
            }
            /////
            if (m_sensitive_vars.size() > 0) {
                std::set<unsigned> intersect;
                // TODO find intersect precond
                if (intersect.size() <= 1) {
                    unsigned max_sz = 0;
                    unsigned largest_pre = 0;
                    for (unsigned i = 0; i < m_partitioning_size; i++) {
                        unsigned cur_sz = 0;
                        expr* e = m_projections[i].get();
                        if (is_app(e)) {
                            app* a = to_app(e);
                            cur_sz = a->get_num_args();
                        }
                        if (cur_sz > max_sz) {
                            max_sz = cur_sz;
                            largest_pre = i;
                        }
                    }
                    intersect.clear();
                    intersect.insert(largest_pre);
                }
                if (DEBUG)
                    std::cout << "found intersect" << *intersect.begin() << std::endl;

                decl2expr_map all_assms;
                expr_ref_vector assigments(m); // for GC
                for (auto& a : m_sensitive_vars) {
                    //expr_set cnjs;
                    //for (int b : intersect) getConj(m_skolem_constraints[a][b], cnjs);
                    expr_ref def = get_assignment_for_var(a, m_subst[*intersect.begin()][a]); //m_skolem_constraints[a][*intersect.begin()].get()
                    all_assms.insert(a, def);
                    assigments.push_back(def);
                    if (DEBUG)
                        std::cout << " crn var: " << a->get_name() << " == " << mk_ismt2_pp(def, m, 3) << std::endl;
                }

                expr_ref bigSkol = combine_assignments(all_assms, m_eval[*intersect.begin()]);
                if (DEBUG)
                    std::cout << "bigSkol: " << mk_ismt2_pp(bigSkol, m, 3) << std::endl;

                for (unsigned i = 0; i < m_partitioning_size; ++i) {
                    all_assms.reset(); //allAssms = sameAssms;

                    if (find(intersect.begin(), intersect.end(), i) == intersect.end()) {
                        for (auto& a : m_sensitive_vars) {
                            expr_ref def = get_assignment_for_var(a, m_subst[i][a]);
                            all_assms.insert(a, def);
                            assigments.push_back(def);
                        }
                        bigSkol = m.mk_ite(m_projections[i].get(), combine_assignments(all_assms, m_eval[i]), bigSkol);
                        //if (compact) bigSkol = u.simplifyITE(bigSkol);
                    }
                }

                std::cout << "RESULT: " << mk_ismt2_pp(m.mk_and(bigSkol, m_skol_scope), m, 3) << std::endl;
                if (DEBUG)
                    std::cout << "m_constraints: " << m_constraints << std::endl;
                if (DEBUG)
                    std::cout << "Sanity check: " << m_utils.implies(m.mk_and(bigSkol, m_skol_scope), m_constraints) << "\n";
                return expr_ref(m.mk_and(bigSkol, m_skol_scope), m);
            }

            return expr_ref(m);
        }

        expr_ref combine_assignments(decl2expr_map& allAssms, decl2expr_map& evals)
        {
            expr_ref_vector skolTmp(m);
            /*ExprMap cyclicSubsts;
      splitDefs(allAssms, cyclicSubsts);

      breakCyclicSubsts(cyclicSubsts, evals, allAssms);
      assert (cyclicSubsts.empty());*/
            for (auto& a : m_sensitive_vars) {
                //assert (emptyIntersect(allAssms[a], v));
                skolTmp.push_back(m.mk_eq(m.mk_const(a), allAssms[a]));
            }
            return m_utils.con_join(skolTmp);
        }

        expr_ref get_assignment_for_var(func_decl* var, expr* e)
        {
            if (DEBUG)
                std::cout << "get_assignment_for_var: " << var->get_name() << " : " << mk_ismt2_pp(e, m, 3) << std::endl;
            arith_util arith(m);
            bool isInt = arith.is_int(var->get_range());
            std::cout << "isInt " << isInt << std::endl;
            expr_ref_vector cnjs(m);
            if (m.is_and(e)) {
                get_conj(e, cnjs);
            } else {
                cnjs.push_back(e);
            }

            //if(m.is_and(e))
            //{

            //TODO removeRedundantConjuncts

            expr_ref_vector conjLT(m);
            expr_ref_vector conjLE(m);
            expr_ref_vector conjGT(m);
            expr_ref_vector conjGE(m);
            expr_ref_vector conjNEQ(m);
            expr_ref_vector conjEQ(m);
            bool incomplete = false;

            for (auto& cnj : cnjs) {
                incomplete = false;
                if (DEBUG)
                    std::cout << "cnj: " << mk_ismt2_pp(cnj, m, 3) << std::endl;
                expr_ref cnj_r = m_utils.mover(cnj, var);
                if (DEBUG)
                    std::cout << "cnj_r: " << mk_ismt2_pp(cnj_r, m, 3) << std::endl;
                expr_ref cnj_r2 = m_utils.ineq_reverter(cnj_r);
                if (DEBUG)
                    std::cout << "cnj2: " << mk_ismt2_pp(cnj_r2, m, 3) << std::endl;

                expr* left = to_app(cnj_r2)->get_arg(0);
                expr* right = to_app(cnj_r2)->get_arg(1);

                if (is_app(left) /*&& to_app(left)->get_decl() == var*/) {

                    if (m.is_not(cnj_r2)) {

                        expr* not_cnj = to_app(cnj_r2)->get_arg(0);
                        if (m.is_eq(not_cnj)) {
                            conjNEQ.push_back(to_app(not_cnj)->get_arg(1));
                        } else // TODO
                            std::cerr << " not yet implemented NEG for assigment of var" << std::endl;
                    }

                    if (m.is_eq(cnj_r2)) {
                        conjEQ.push_back(right);
                    } else if (arith.is_le(cnj_r2)) {
                        conjLE.push_back(right);
                    } else if (arith.is_lt(cnj_r2)) {
                        conjLT.push_back(right);
                    } else if (arith.is_ge(cnj_r2)) {
                        conjGE.push_back(right);
                    } else if (arith.is_gt(cnj_r2)) {
                        conjGT.push_back(right);
                    }
                } else
                    incomplete = true;
                if (incomplete && DEBUG) {
                    std::cerr << "WARNING: This constraint is unsupported: " << mk_ismt2_pp(cnj_r2, m, 3) << "\n";
                }
            }

            // simplify some:
            for (auto& b : conjLE) {
                bool toBrk = false;
                for (auto& a : conjNEQ) {
                    if (m.are_equal(a, b)) //a == b
                    {
                        conjLT.push_back(a);
                        conjNEQ.erase(a);
                        conjLE.erase(b);
                        toBrk = true;
                        break;
                    }
                }
                if (toBrk)
                    break;
            }

            // simplify some:
            for (auto& b : conjGE) {
                bool toBrk = false;
                for (auto& a : conjNEQ) {
                    if (m.are_equal(a, b)) //a == b
                    {
                        conjGT.push_back(a);
                        conjNEQ.erase(a);
                        conjGE.erase(b);
                        toBrk = true;
                        break;
                    }
                }
                if (toBrk)
                    break;
            }

            // get the assignment (if exists)

            if (conjEQ.size() > 0)
                return expr_ref(conjEQ.get(0), m); // GF: maybe try to find the best of them

            expr_ref curMaxGT(m);
            if (conjGT.size() > 1) {
                get_symbolic_max(conjGT, curMaxGT, isInt);
            } else if (conjGT.size() == 1) {
                curMaxGT = *(conjGT.begin());
            }
            expr_ref curMaxGE(m);
            if (conjGE.size() > 1) {
                get_symbolic_max(conjGE, curMaxGE, isInt);
            } else if (conjGE.size() == 1) {
                curMaxGE = *(conjGE.begin());
            }

            expr_ref curMinLT(m);
            if (conjLT.size() > 1) {
                get_symbolic_min(conjLT, curMinLT, isInt);
            } else if (conjLT.size() == 1) {
                curMinLT = *(conjLT.begin());
            }

            expr_ref curMinLE(m);
            if (conjLE.size() > 1) {
                get_symbolic_min(conjLE, curMinLE, isInt);
            } else if (conjLE.size() == 1) {
                curMinLE = *(conjLE.begin());
            }

            expr_ref curMax(m);
            expr_ref curMin(m);

            if (curMaxGT != 0 && curMaxGE != 0) {
                curMax = m.mk_ite(arith.mk_gt(curMaxGT, curMaxGE), curMaxGT, curMaxGE);
            } else if (curMaxGT != 0)
                curMax = curMaxGT;
            else
                curMax = curMaxGE;

            if (curMinLT != 0 && curMinLE != 0) {
                curMin = m.mk_ite(arith.mk_lt(curMinLT, curMinLE), curMinLT, curMinLE);
            } else if (curMinLT != 0)
                curMin = curMinLT;
            else
                curMin = curMinLE;

            if (DEBUG) {
                std::cout << "curMin: " << mk_ismt2_pp(curMin, m, 3) << std::endl;
                std::cout << "curMax: " << mk_ismt2_pp(curMax, m, 3) << std::endl;
            }
            if (conjNEQ.size() == 0) {
                if (curMinLT == 0 && curMinLE != 0) {
                    return curMinLE;
                }

                if (curMaxGT == 0 && curMaxGE != 0) {
                    return curMaxGE;
                }

                if (curMinLT != 0 && curMinLE == 0 && curMaxGT == 0 && curMaxGE == 0) {
                    return m_utils.minus_eps(curMinLT, isInt);
                }

                if (curMinLT == 0 && curMinLE == 0 && curMaxGT != 0 && curMaxGE == 0) {
                    return m_utils.plus_eps(curMaxGT, isInt);
                }

                if (curMinLT != 0 && curMinLE != 0 && curMaxGT == 0 && curMaxGE == 0) {
                    return m_utils.minus_eps(curMin, isInt);
                }

                if (curMinLT == 0 && curMinLE == 0 && curMaxGT != 0 && curMaxGE != 0) {
                    return m_utils.plus_eps(curMax, isInt);
                }

                if (curMinLT != 0 && curMinLE == 0 && curMaxGT != 0 && curMaxGE == 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMinLT, curMaxGT), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMinLT, curMaxGT), arith.mk_real(2)), m);
                }

                if (curMinLT == 0 && curMinLE != 0 && curMaxGT == 0 && curMaxGE != 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMinLE, curMaxGE), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMinLE, curMaxGE), arith.mk_real(2)), m);
                }

                if (curMinLT == 0 && curMinLE != 0 && curMaxGT != 0 && curMaxGE == 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMinLE, curMaxGT), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMinLE, curMaxGT), arith.mk_real(2)), m);
                }

                if (curMinLT != 0 && curMinLE == 0 && curMaxGT == 0 && curMaxGE != 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMinLT, curMaxGE), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMinLT, curMaxGE), arith.mk_real(2)), m);
                }

                if (curMinLT != 0 && curMinLE == 0 && curMaxGT != 0 && curMaxGE != 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMinLT, curMax), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMinLT, curMax), arith.mk_real(2)), m);
                }

                if (curMinLT == 0 && curMinLE != 0 && curMaxGT != 0 && curMaxGE != 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMinLE, curMax), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMinLE, curMax), arith.mk_real(2)), m);
                }

                if (curMinLT != 0 && curMinLE != 0 && curMaxGT == 0 && curMaxGE != 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMin, curMaxGE), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMin, curMaxGE), arith.mk_real(2)), m);
                }

                if (curMinLT != 0 && curMinLE != 0 && curMaxGT != 0 && curMaxGE == 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMin, curMaxGT), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMin, curMaxGT), arith.mk_real(2)), m);
                }

                if (curMinLT != 0 && curMinLE != 0 && curMaxGT != 0 && curMaxGE != 0) {
                    if (isInt)
                        return expr_ref(arith.mk_idiv(arith.mk_add(curMin, curMax), arith.mk_int(2)), m);
                    else
                        return expr_ref(arith.mk_div(arith.mk_add(curMin, curMax), arith.mk_real(2)), m);
                }
                //assert(0);
            }

            // here conjNEQ.size() > 0
            //TODO



            //}
            /*else
        {

            std::cerr << "not yet implemented"<<std::endl;
        }*/

            return expr_ref(0, m);
        }

        void get_conj(expr* e, expr_ref_vector& vec_out)
        {
            if (m.is_and(e)) {
                app* a = to_app(e);
                //for(auto arg: *a)
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    expr* arg = *(a->get_args() + i);
                    get_conj(arg, vec_out);
                }
            } else if (m.is_false(e)) {
                vec_out.reset();
                vec_out.push_back(e);
            } else {
                if (DEBUG)
                    std::cout << "get_conj: " << mk_ismt2_pp(e, m, 3) << std::endl;
                vec_out.push_back(e);
            }
        }

    public:
        /**
     * Self explanatory
     */
        void get_symbolic_max(expr_ref_vector& vec, expr_ref& curMax, bool isInt)
        {

            curMax = *vec.begin();
            for (auto it = vec.begin(); ++it != vec.end();) {
                auto& a = *it;
                if (m_utils.is_equil(m_arith.mk_lt(curMax, a), m.mk_true())) {
                    curMax = a;
                } else if (m_utils.is_equil(m_arith.mk_lt(curMax, a), m.mk_false())) {
                    //  curMax is OK
                } else {
                    std::string ind = std::to_string(m_fresh_var_ind++);

                    std::string fresh_varname = "_aeval_tmp_max_" + ind;
                    expr* var_app = m.mk_const(fresh_varname, isInt ? m_arith.mk_int() : m_arith.mk_real());
                    expr* newConstr = m.mk_eq(var_app, m.mk_ite(m_arith.mk_lt(curMax, a), a, curMax));
                    m_skol_scope = m.mk_and(m_skol_scope, newConstr); //simplifiedAnd(skolSkope, newConstr);

                    curMax = var_app;
                }
            }
        }

        /**
     * Self explanatory
     */
        void get_symbolic_min(expr_ref_vector& vec, expr_ref& curMin, bool isInt)
        {
            curMin = *vec.begin();
            for (auto it = vec.begin(); ++it != vec.end();) {
                auto& a = *it;
                if (m_utils.is_equil(m_arith.mk_gt(curMin, a), m.mk_true())) {
                    curMin = a;
                } else if (m_utils.is_equil(m_arith.mk_gt(curMin, a), m.mk_false())) {
                    //  curMin is OK
                } else {
                    std::string ind = std::to_string(m_fresh_var_ind++);

                    std::string fresh_varname = "_aeval_tmp_min_" + ind;
                    expr* var_app = m.mk_const(fresh_varname, isInt ? m_arith.mk_int() : m_arith.mk_real());

                    expr* newConstr = m.mk_eq(var_app, m.mk_ite(m_arith.mk_gt(curMin, a), a, curMin));
                    m_skol_scope = m.mk_and(m_skol_scope, newConstr); // simplifiedAnd(skolSkope, newConstr);
                    curMin = var_app;
                }
            }
        }
        bool sameBoolOrCmp(expr* e1, expr* e2)
        {
            //TODO: Cmp Operation or Bool Operation
            return false;
        }

        expr_ref ineqNegReverter(expr* a)
        {
            /* if (isOpX<NEG>(a)){
        Expr e = a->arg(0);
        if (isOpX<LEQ>(e)){
          return mk<GT>(e->arg(0), e->arg(1));
        } else if (isOpX<GEQ>(e)){
          return mk<LT>(e->arg(0), e->arg(1));
        } else if (isOpX<LT>(e)){
          return mk<GEQ>(e->arg(0), e->arg(1));
        } else if (isOpX<GT>(e)){
          return mk<LEQ>(e->arg(0), e->arg(1));
        } else if (isOpX<NEQ>(e)){
          return mk<EQ>(e->arg(0), e->arg(1));
        } else if (isOpX<EQ>(e)){
          return mk<NEQ>(e->arg(0), e->arg(1));
        }
      }*/
            return expr_ref(a, m);
        }
    };

    struct invocations_rewriter_cfg : public default_rewriter_cfg {
    private:
        ast_manager& m;
        expr_ref_vector m_pinned;
        func_decl_ref_vector& m_synth_fun_list;
        func_decl_ref_vector& m_subs;
        obj_map<func_decl, func_decl*>& m_synth_fun_sub_map;

    public:
        invocations_rewriter_cfg(ast_manager& m,
            func_decl_ref_vector& synth_fun_list,
            func_decl_ref_vector& subs,
            obj_map<func_decl, func_decl*>& synth_fun_sub_map)
            : m(m)
            , m_pinned(m)
            , m_synth_fun_list(synth_fun_list)
            , m_subs(subs)
            , m_synth_fun_sub_map(synth_fun_sub_map)
        {
        }

        bool get_subst(expr* s, expr*& t, proof*& t_pr)
        {
            if (!is_app(s)) {
                return false;
            }
            app* a = to_app(s);
            func_decl* sym = a->get_decl();
            func_decl* sub;
            if (!find_in_synth_fun(sym, sub)) {
                return false;
            }
            app* a_sub = m.mk_const(sub);
            t = to_expr(a_sub);
            if(DEBUG)
                std::cout << "\t get_subst: " << mk_ismt2_pp(s, m, 3) << std::endl;

            return true;
        }

    private:
        bool find_in_synth_fun(func_decl* sym, func_decl*& sub)
        {
            for (unsigned i = 0; i < m_synth_fun_list.size(); ++i) {
                func_decl* dst = m_synth_fun_list[i].get();
                if (dst->get_name() == sym->get_name()) { // for single-invocation
                    sub = get_surrogate(dst);
                    return true;
                }
            }
            return false;
        }

        func_decl* get_surrogate(func_decl* f) const
        {
            obj_map<func_decl, func_decl*>::iterator it = m_synth_fun_sub_map.find_iterator(f);
            if (it != m_synth_fun_sub_map.end())
                return it->m_value;
            return nullptr;
        }
    };
}

class aevall_solver_context {
    cmd_context& m_cmd;
    ast_manager& m;
    expr_ref_vector m_constraints_list;
    func_decl_ref_vector m_synth_fun_list;

    func_decl_ref_vector m_subs;
    obj_map<func_decl, func_decl*> m_synth_fun_sub_map;

    params_ref m_params;
    ref<solver> m_solver;

public:
    aevall_solver_context(cmd_context& cmd_ctx)
        : m_cmd(cmd_ctx)
        , m(cmd_ctx.m())
        , m_constraints_list(m)
        , m_synth_fun_list(m)
        , m_subs(m)
    {
    }

    void register_synth_fun(func_decl* pred)
    {
        if(DEBUG)
            std::cout << "register_synth_fun: " << pred->get_name() << "(" << pred->get_arity() << "):" << pred->get_range()->get_name() << std::endl;
        m_synth_fun_list.push_back(pred);
    }

    void add_constraint(expr* constraint)
    {
        if(DEBUG)
            std::cout << "add_constraint: " << mk_ismt2_pp(constraint, m, 2) << std::endl;
        m_constraints_list.push_back(constraint);
    }

    bool check_synth()
    {
        std::cout << "(check synth) " << std::endl;
        if (m_synth_fun_list.size() == 0) {
            //todo
            return false;
        }
        fill_subs();


        expr_ref all_constraints(m);
        if (m_constraints_list.size() > 1)
            all_constraints = m.mk_and(m_constraints_list.size(), m_constraints_list.c_ptr());
        else {
            all_constraints = m_constraints_list[0].get();
        }
        expr_ref new_expr(m);
        rewrite_expr(all_constraints.get(), new_expr);
        if(DEBUG)
            std::cout << "new_expr: " << mk_ismt2_pp(new_expr, m, 2) << std::endl;

        if (!m_solver) {
            m_solver = m_cmd.get_solver_factory()(m, m_params, false, true, false, symbol::null);
        }
        aevall_solver ae(m_cmd, m, m_solver.get());
        ae.solve(m_subs, new_expr);
        return false;
    }

    void rewrite_expr(expr* f, expr_ref& res)
    {
        invocations_rewriter_cfg inv_cfg(m, m_synth_fun_list, m_subs, m_synth_fun_sub_map);
        rewriter_tpl<invocations_rewriter_cfg> rwr(m, false, inv_cfg);
        rwr(f, res);
    }

private:
    void fill_subs()
    {
        m_subs.reset();
        m_synth_fun_sub_map.reset();
        for (unsigned i = 0; i < m_synth_fun_list.size(); ++i) {
            func_decl* dst = m_synth_fun_list[i].get();
            func_decl_ref sub(
                m.mk_const_decl(dst->get_name(), dst->get_range()), m);
            m_subs.push_back(sub);
            m_synth_fun_sub_map.insert(dst, sub);
        }
    }
};
}

struct aeval_context {
    //smt_params                    m_fparams;
    params_ref m_params_ref;
    fp_params m_params;
    cmd_context& m_cmd;

    unsigned m_ref_count;
    scoped_ptr<aeval::aevall_solver_context> m_context;
    trail_stack<aeval_context> m_trail;

    /*fp_params const& get_params() {
        init();
        return m_context->get_params();
    }*/

    aeval_context(cmd_context& ctx)
        : m_params(m_params_ref)
        , m_cmd(ctx)
        , m_ref_count(0)
        , m_trail(*this)
    {
    }

    void inc_ref()
    {
        ++m_ref_count;
    }

    void dec_ref()
    {
        --m_ref_count;
        if (0 == m_ref_count) {
            dealloc(this);
        }
    }

    void init()
    {
        ast_manager& m = m_cmd.m();
        if (!m_context) {
            m_context = alloc(aeval::aevall_solver_context, m_cmd);
        }
        /*if (!m_decl_plugin) {
            symbol name("datalog_relation");
            if (m.has_plugin(name)) {
                m_decl_plugin = static_cast<datalog::dl_decl_plugin*>(m_cmd.m().get_plugin(m.mk_family_id(name)));
            }
            else {
                m_decl_plugin = alloc(datalog::dl_decl_plugin);
                m.register_plugin(symbol("datalog_relation"), m_decl_plugin);
            }
        }*/
    }

    void reset()
    {
        m_context = nullptr;
    }

    void push()
    {
        m_trail.push_scope();
        //dlctx().push();
    }

    void pop()
    {
        m_trail.pop_scope(1);
        // dlctx().pop();
    }

    aeval::aevall_solver_context& aectx()
    {
        init();
        return *m_context;
    }
};

/**
   \brief constraint command. It is also the owner of dl_context object.
*/
class sl_constraint_cmd : public cmd {
    ref<aeval_context> m_aeval_ctx;
    mutable unsigned m_arg_idx;
    expr* m_t;

public:
    sl_constraint_cmd(aeval_context* aeval_ctx)
        : cmd("constraint")
        , m_aeval_ctx(aeval_ctx)
        , m_arg_idx(0)
        , m_t(nullptr)
    {
    }
    char const* get_usage() const override { return "(constraint <expr>)"; }
    char const* get_descr(cmd_context& ctx) const override { return "add a constraint"; }
    unsigned get_arity() const override { return 1; }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override
    {
        return CPK_EXPR;
    }
    void set_next_arg(cmd_context& ctx, expr* t) override
    {
        m_t = t;
        m_arg_idx++;
    }

    void reset(cmd_context& ctx) override
    {
        m_aeval_ctx->reset();
        prepare(ctx);
        m_t = nullptr;
    }
    void prepare(cmd_context& ctx) override { m_arg_idx = 0; }
    void finalize(cmd_context& ctx) override
    {
    }
    void execute(cmd_context& ctx) override
    {
        if (!m_t)
            throw cmd_exception("invalid constraint, expected formula");
        m_aeval_ctx->aectx().add_constraint(m_t);
    }
};

class sl_check_synth_cmd : public cmd {
    ref<aeval_context> m_aeval_ctx;
    unsigned m_arg_idx;
    mutable unsigned m_query_arg_idx;
    symbol m_fun_name;
    svector<sorted_var> m_sorted_var_list;
    sort* m_var_sort;

public:
    sl_check_synth_cmd(aeval_context* aeval_ctx)
        : cmd("check-synth")
        , m_aeval_ctx(aeval_ctx)
    {
    }

    char const* get_usage() const override { return "(check-synth)"; }
    char const* get_descr(cmd_context& ctx) const override { return "initializes synthesis"; }
    unsigned get_arity() const override { return 0; }

    void prepare(cmd_context& ctx) override
    {
        ctx.m(); // ensure manager is initialized.
    }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override
    {
        return CPK_UINT;
    }

    void execute(cmd_context& ctx) override
    {
        if (m_arg_idx < 3) {
            throw cmd_exception("at least 3 arguments expected");
        }

        m_aeval_ctx->aectx().check_synth();
    }
};

class sl_synth_fun_cmd : public cmd {
    ref<aeval_context> m_aeval_ctx;
    unsigned m_arg_idx;
    mutable unsigned m_query_arg_idx;
    symbol m_fun_name;
    svector<sorted_var> m_sorted_var_list;
    sort* m_var_sort;

public:
    sl_synth_fun_cmd(aeval_context* aeval_ctx)
        : cmd("synth-fun")
        , m_aeval_ctx(aeval_ctx)
    {
    }

    char const* get_usage() const override { return "<symbol> (<arg1 sort> ...) <representation>*"; }
    char const* get_descr(cmd_context& ctx) const override { return "declare new relation"; }
    unsigned get_arity() const override { return 3; }

    void prepare(cmd_context& ctx) override
    {
        ctx.m(); // ensure manager is initialized.
        m_arg_idx = 0;
        m_query_arg_idx = 0;
        m_sorted_var_list.reset();
    }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override
    {
        switch (m_query_arg_idx++) {
        case 0:
            return CPK_SYMBOL; // fun name
        case 1:
            return CPK_SORTED_VAR_LIST; // arguments
        case 2:
            return CPK_SORT; // sort of fun
        default:
            return CPK_SORT; // sort of fun
        }
    }
    void set_next_arg(cmd_context& ctx, unsigned num, sorted_var const* slist) override
    {
        m_sorted_var_list.reset();
        m_sorted_var_list.append(num, slist);
        m_arg_idx++;
    }
    void set_next_arg(cmd_context& ctx, symbol const& s) override
    {
        if (m_arg_idx == 0) {
            m_fun_name = s;
        } else {
            //SASSERT(m_arg_idx>1);
            //m_kinds.push_back(s);
        }
        m_arg_idx++;
    }

    void set_next_arg(cmd_context& ctx, sort* s) override
    {
        m_var_sort = s;
        ++m_arg_idx;
    }

    void execute(cmd_context& ctx) override
    {
        if (m_arg_idx < 3) {
            throw cmd_exception("at least 3 arguments expected");
        }
        ast_manager& m = ctx.m();
        sort_ref_vector domain(m);
        for (unsigned int i = 0; i < m_sorted_var_list.size(); ++i) {
            domain.push_back(m_sorted_var_list[i].second);
        }
        func_decl_ref sf(
            m.mk_func_decl(m_fun_name, domain.size(), domain.c_ptr(), m_var_sort), m);
        ctx.insert(sf);
        m_aeval_ctx->aectx().register_synth_fun(sf);
    }
};

class sl_declare_var_cmd : public cmd {
    unsigned m_arg_idx;
    symbol m_var_name;
    sort* m_var_sort;
    ref<aeval_context> m_aeval_ctx;

public:
    sl_declare_var_cmd(aeval_context* sl_ctx)
        : cmd("declare-var")
        , m_arg_idx(0)
        , m_aeval_ctx(sl_ctx)
    {
    }

    char const* get_usage() const override { return "<symbol> <sort>"; }
    char const* get_descr(cmd_context& ctx) const override { return "declare constant as variable"; }
    unsigned get_arity() const override { return 2; }

    void prepare(cmd_context& ctx) override
    {
        ctx.m(); // ensure manager is initialized.
        m_arg_idx = 0;
    }
    cmd_arg_kind next_arg_kind(cmd_context& ctx) const override
    {
        SASSERT(m_arg_idx <= 1);
        if (m_arg_idx == 0) {
            return CPK_SYMBOL;
        }
        return CPK_SORT;
    }

    void set_next_arg(cmd_context& ctx, sort* s) override
    {
        m_var_sort = s;
        ++m_arg_idx;
    }

    void set_next_arg(cmd_context& ctx, symbol const& s) override
    {
        m_var_name = s;
        ++m_arg_idx;
    }

    void execute(cmd_context& ctx) override
    {
        ast_manager& m = ctx.m();
        func_decl_ref var(m.mk_func_decl(m_var_name, 0, static_cast<sort* const*>(nullptr), m_var_sort), m);
        ctx.insert(var);
        //m_aeval_ctx->dlctx().register_variable(var);
    }
};

static void install_aeval_cmds_aux(cmd_context& ctx)
{
    aeval_context* sl_ctx = alloc(aeval_context, ctx);
    ctx.insert(alloc(sl_constraint_cmd, sl_ctx));
    ctx.insert(alloc(sl_check_synth_cmd, sl_ctx));
    ctx.insert(alloc(sl_synth_fun_cmd, sl_ctx));
    ctx.insert(alloc(sl_declare_var_cmd, sl_ctx));
}

void install_aeval_cmds(cmd_context& ctx)
{
    install_aeval_cmds_aux(ctx);
}
