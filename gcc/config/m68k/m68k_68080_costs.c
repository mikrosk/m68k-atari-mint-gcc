#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "cfghooks.h"
#include "tree.h"
#include "rtl.h"
#include "insn-modes.h"

bool
m68k_68080_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed);
#if 1
static int ttotal;
#define TEST(a,r) {ttotal = 0; m68k_68080_costs(a, SImode, 0, 0, &ttotal, 1); if (ttotal != r) printf("%d <> %d: %s\n", ttotal, r, #a);}

void
selftest_m68k_68080_costs (void)
{
  rtx d0 = gen_rtx_REG (SImode, 0);
  rtx d1 = gen_rtx_REG (SImode, 1);
  rtx a0 = gen_rtx_REG (SImode, 8);

  rtx c120 = gen_rtx_CONST_INT(VOIDmode, 120);

  rtx mem_120ia0 = gen_rtx_MEM(SImode, gen_rtx_PLUS(SImode, a0, c120));

  rtx movel_d0_d1 = gen_rtx_SET(d1, d0);
  TEST(movel_d0_d1, 4);

  rtx add_d0_d1 = gen_rtx_SET(d1, gen_rtx_PLUS(SImode, d1, d0));
  TEST(add_d0_d1, 4);

  rtx movel_120ia0_d0 = gen_rtx_SET(d0, mem_120ia0);
  TEST(movel_120ia0_d0, 8);

}
static int run;
#endif

/**
 * calculate costs for the 68080.
 * opno == 1: calculate as if dst is a register
 * opno == 0: calculate difference to register assignment
 */
bool
m68k_68080_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed)
{
  if (!run)
    {
      run = 1;
      selftest_m68k_68080_costs ();
    }

  int code = GET_CODE(x);
  int total2 = 0;
  *total = 0;
  switch (code)
    {
    case CC0:
    case PC:
    case REG:
      *total = 2;
      return true;

    case CONST_INT:
      {
	int iv = INTVAL(x);

	// moveq
	if (outer_code == SET && iv >= -0x100 && iv <= 0xff)
	  *total = 2;
	else
	// addq
	if ((outer_code == PLUS || outer_code == MINUS) && iv >= -0x8
	    && iv <= 0x7)
	  *total = 2;
	else
	// .b .w *iw.l
	if (GET_MODE_SIZE(mode) < 4 && iv >= -32768 && iv <= 32767)
	  *total = 3;
	else
	  *total = 4;
      }
      return true;

    case CONST_DOUBLE:
      *total = mode == SFmode ? 6 : mode == DFmode ? 8 : 10;
      return true;

    case FLOAT:
    case FLOAT_TRUNCATE:
    case FIX:
      *total = 8; // guessed
      return true;

    case MULT:
      {
	rtx op = XEXP(x, 0);
	if (CONST_INT_P(op) && exact_log2 (INTVAL(op)))
	  total2 = 0; // same as shift
	else
	  total2 = 8;
	goto OpCost;
      }
      break;

    case UDIV:
    case MOD:
    case DIV:
      total2 = 30; // always in a parallel with DIV and MOD -> half costs
      // with regs, 2 are added by the caller and 2 by the code below
      goto OpCost;

    case ASHIFT:
    case ASHIFTRT:
    case LSHIFTRT:
    case PLUS:
    case MINUS:
    case AND:
    case IOR:
    case XOR:
      {
	OpCost: rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);

	// reg or mem
	m68k_68080_costs (a, mode, code, 0, total, speed);
	total2 += *total;

	// add cost for 2nd
	m68k_68080_costs (a, mode, code, 0, total, speed);
	*total += total2;
	return true;
      }
      break;

    case SUBREG:
    case STRICT_LOW_PART:
    case SIGN_EXTRACT:
    case ZERO_EXTRACT:
    case TRUNCATE:
    case ZERO_EXTEND:
    case NOT:
    case NEG:
    case SIGN_EXTEND:
    case CONST:
      // no additional cost
      return m68k_68080_costs (XEXP(x, 0), mode, code, 0, total, speed);

    case CALL:
      {
	// does not matter
	*total = 16;
	return true;
      }

    case MEM:
      {
	rtx a = XEXP(x, 0);
	if (REG_P(a) || GET_CODE(a) == POST_INC
	    || GET_CODE(a) == PRE_DEC)
	  {
	    *total = 5; // (ax), (ax)+, -(ax)
	    return true;
	  }
	if (GET_CODE(a) == SYMBOL_REF || GET_CODE(a) == LABEL_REF)
	  {
	    *total = 9;
	    return true;
	  }
	if (GET_CODE(a) == PLUS)
	  {
	    rtx b = XEXP(a, 0);
	    rtx c = XEXP(a, 1);
	    if (REG_P(b) && GET_CODE(c) == CONST_INT && INTVAL(c) >= -32768
		&& INTVAL(c) <= 37267)
	      {
		*total = 6; // 16(An),Dn
		return true;
	      }
	    if (REG_P(b) || GET_CODE(b) == MULT || GET_CODE(b) == ASHIFT)
	      {
		if (REG_P(c))
		  {
		    *total = 8; // (An,Xn*S)
		    return true;
		  }
		if (REG_P(c) || GET_CODE(c) == SYMBOL_REF || GET_CODE(c) == CONST_INT)
		  {
		    *total = 10; // (32,Xn*S)
		    return true;
		  }
	      }
	    if (GET_CODE(b) == PLUS)
	      {
		rtx b0 = XEXP(b, 0);
		rtx b1 = XEXP(b, 1);
		if (REG_P(b0) || GET_CODE(b0) == MULT || GET_CODE(b0) == ASHIFT)
		  {
		    if (GET_CODE(c) == CONST_INT)
		      {
			*total = INTVAL(c) >= -8 && INTVAL(c) <= 7 ? 8 // 8(An,Xn*S)
			    :
				 INTVAL(c) >= -32768 && INTVAL(c) <= 32767 ? 9 // (16,An,Xn*S)
				     : 10; // (32,An,Xn*S)
			return true;
		      }
		    if (GET_CODE(c) == SYMBOL_REF)
		      {
			*total = 10;
			return true;
		      }
		  }
	      }
	  }
	*total = 38;
	return true;
      }
      break;

    case SYMBOL_REF:
    case LABEL_REF:
      *total = 4;
      return true;

    case COMPARE:
    case SET:
      {
	rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);
	bool r = m68k_68080_costs (a, mode, code, 0, total, speed);
	total2 = *total;

	if (code == SET)
	switch (GET_CODE(b))
	{
	  case ASHIFT:
	  case ASHIFTRT:
	  case LSHIFTRT:
	  case PLUS:
	  case MINUS:
	  case AND:
	  case IOR:
	  case XOR:
	    total2 = 0;
	    break;
	  default:
	    break;
	}

	r &= m68k_68080_costs (b, mode, code, 0, total, speed);
	*total += total2;

	if (GET_CODE(b) == COMPARE)
	  *total -= 2;

	// lea penalty
	if (REG_P(a) && GET_CODE(b) == PLUS && XEXP(b, 0) != a)
	  *total += 1;



	return r;
      }
      break;

    case IF_THEN_ELSE:
      *total = 16; // bcc
      return true;

    case ASM_OPERANDS:
    case ASM_INPUT:
      return false;
    }
  return false;
}
