#!/usr/bin/env python3

from typing import Optional
from symbolic import box, Result
from tinyscript_util import (
	check_sat,
	stringify,
	fmla_stringify,
	fmla_enc,
	state_from_z3_model
)
from interpreter import exc
import tinyscript as tn
import z3

# Global variables
STEPS_LEFT = "#steps_left"

def ins_to_add():
	decrementSteps = tn.Asgn(STEPS_LEFT, tn.Difference(tn.Var(STEPS_LEFT), tn.Const(1)))
	return decrementSteps

def add_instrumentation(alpha: tn.Prog, step_bound: Optional[int]=None) -> tn.Prog:
	match alpha:
		case tn.Asgn(name, e):
			return tn.Seq(ins_to_add(), alpha)

		case tn.Skip():
			return tn.Seq(ins_to_add(), alpha)

		case tn.Output(e):
			return tn.Seq(ins_to_add(), alpha)

		case tn.Abort():
			return tn.Seq(ins_to_add(), alpha)

		case tn.Seq(alpha_p, beta_p):
			ins_alpha = add_instrumentation(alpha_p, step_bound)
			ins_beta = add_instrumentation(beta_p, step_bound)
			return tn.Seq(ins_alpha, ins_beta)

		case tn.If(p, alpha_p, beta_p):
			ins_alpha = add_instrumentation(alpha_p, step_bound)
			ins_beta = add_instrumentation(beta_p, step_bound)
			return tn.If(p, ins_alpha, ins_beta)

		case tn.While(q, alpha_p):
			ins_alpha = add_instrumentation(alpha_p, step_bound)
			return tn.While(q, ins_alpha)
	
	# should not ever get here
	return alpha

def instrument(alpha: tn.Prog, step_bound: Optional[int]=None) -> tn.Prog:
	"""
	Instruments a program to support symbolic checking 
	for violations of the maximum execution length policy.
	
	Args:
	    alpha (tn.Prog): A tinyscript program to instrument
	    step_bound (int, optional): A bound on runtime steps
	
	Returns:
	    tn.Prog: The instrumented program. It should be possible
	    	to use the box modality and a satisfiability solver
	    	to determine whether a trace in the original program
	    	`alpha` exists that executes for longer than the bound
	    	on steps. A step occurs when the program executes an
	    	assignment, output, abort, or skip statement.
	"""
	initializeStepsLeft = tn.Asgn(STEPS_LEFT, tn.Const(step_bound))
	ins_alpha = add_instrumentation(alpha, step_bound)
	return tn.Seq(initializeStepsLeft, ins_alpha)

# X="x"
# Y="y"
# initializeX = tn.Asgn(tn.Var(X), 3)
# initializeY = tn.Asgn(tn.Var(Y), 2)
# subtractOneFromX = tn.Asgn(tn.Var(X), tn.Difference(tn.Var(X), tn.Const(1)))
# addOneToY = tn.Asgn(tn.Var(Y), tn.Sum(tn.Var(Y), tn.Const(1)))
# whileLoop = tn.While(tn.LtF(tn.Const(0), tn.Var(X)), tn.Seq(subtractOneFromX, addOneToY))
# program = tn.Seq(tn.Seq(initializeX, initializeY), whileLoop)
# print("PROGRAM", program)

def symbolic_check(
	alpha: tn.Prog, 
	step_bound: int,
	max_depth: int=3,
	timeout: int=1) -> Result:
	"""
	Uses the box modality and a satisfiability solver to determine
	whether there are any traces that execute more than `step_bound`
	steps. A step occurs when the program executes an assignment, 
	output, abort, or skip statement. This function only considers 
	traces generated after unrolling loops up to `max_depth` times, 
	and will terminate the solver after `timeout` seconds.
	
	Args:
	    alpha (tn.Prog): Program to check
	    step_bound (int): Step bound to check
	    max_depth (int, optional): Loop unrolling depth
	    timeout (int, optional): Solver timeout, in seconds
	
	Returns:
	    Result: The status of the check, one of three values:
	    	- Result.Satisfies: All traces, up to the given unrolling 
	    	  depth, terminate within `step_bound` steps. 
	    	- Result.Violates: There exists a trace that violates the
	    	  step bound. This result *includes* traces that do not 
	    	  terminate within the unrolling depth, e.g., 
	    	  the program "while(true) skip" should yield this result
	    	  with an unrolling depth of 1 if the solver is able to 
	    	  provide a state that causes the interpreter to execute
	    	  at least `step_bound` steps.
	    	- Result.Unknown: The result is indeterminate. This could
	    	  mean that the solver timed out, returning z3.unknown. It
	    	  could also signify that there is a trace that fails to
	    	  terminate within the unrolling bound, but the solver did
	    	  not return a state that caused the interpreter to execute
	    	  at least `step_bound` steps.
	"""
	alpha_p = instrument(alpha, step_bound)
	postcondition = tn.LtF(tn.Const(-1), tn.Var(STEPS_LEFT))
	weakest_pre = box(alpha_p, fmla_enc(postcondition), max_depth=max_depth, depth_exceed_strict=True)

	res, model = check_sat([z3.Not(weakest_pre)], timeout=timeout)

	if res == z3.unsat:
		return Result.Satisfies
	# elif res == z3.sat:
	# 	state = state_from_z3_model(alpha, model, complete=True)
	# 	print("state", state)
	# 	final_state = exc(state, alpha_p, max_steps=1.e6, quiet=False)
	# 	if final_state[0].variables[VIOLATED] == 1:
	# 		return Result.Violates
	# return Result.Unknown
	return Result.Violates


if __name__ == "__main__":
	from parser import parse, fmla_parse
	import sys
	from pathlib import Path

	# TEST_DIR = Path('.') / 'tests'
	TEST_DIR = Path('.') / 'test'

	if not TEST_DIR.is_dir():
		raise ValueError(f"Expected {TEST_DIR} to be a directory")

	passed = 0
	violate = 0
	unknown = 0

	for test_file in list(TEST_DIR.iterdir()):
		if not str(test_file).endswith('tinyscript'):
			continue
		with test_file.open() as f:
			prog = parse(f.read())
# test
			alpha_p = instrument(prog, 100)
			print("INSPROGRAM:\n", stringify(alpha_p))
# test



			res = symbolic_check(prog, 100)
			print((
				f"{test_file} result:" 
				f"{res}"))

			match res:
				case Result.Satisfies:
					passed += 1
				case Result.Violates:
					violate += 1
				case Result.Unknown:
					unknown += 1

	print(f"\n{passed=}, {violate=}, {unknown=}")

	# X="x"
	# Y="y"
	# Z = "z"
	# initializeX = tn.Asgn(X, tn.Const(3))
	# initializeY = tn.Asgn(Y, tn.Const(2))
	# initializeZ = tn.Asgn(X, tn.Const(1))
	# subtractOneFromX = tn.Asgn(X, tn.Difference(tn.Var(X), tn.Const(1)))
	# addOneToY = tn.Asgn(Y, tn.Sum(tn.Var(Y), tn.Const(1)))
	# whileLoop = tn.While(tn.LtF(tn.Const(0), tn.Var(Z)), subtractOneFromX)
	# program = tn.Seq(tn.Seq(initializeX, initializeZ), whileLoop)


	# STEP_BOUND = 5
	# # program = tn.Seq(initializeX, initializeY)
	# print("PROGRAM:\n", stringify(program))
	# ins_prog:tn.Prog = instrument(program, STEP_BOUND)
	# print("\n")
	# print("INSPROGRAM:\n", stringify(ins_prog))
	# res = symbolic_check(program, STEP_BOUND)
	# print("\n")
	# print("RES", res)