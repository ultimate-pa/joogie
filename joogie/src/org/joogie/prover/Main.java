package org.joogie.prover;

import org.joogie.prover.princess.PrincessProverFactory;

public class Main {

	public static void main(String[] args) {
		final ProverFactory factory = new PrincessProverFactory();
		final Prover p = factory.spawn();
		p.getBooleanType();

		final ProverExpr c = p.mkVariable("c", p.getIntType());
		final ProverExpr d = p.mkVariable("d", p.getIntType());
		final ProverExpr r = p.mkVariable("r", p.getBooleanType());
		final ProverExpr s = p.mkVariable("s", p.getBooleanType());

		p.addAssertion(p.mkAnd(r, p.mkEq(c, p.mkPlus(d, p.mkLiteral(15)))));
		p.addAssertion(p.mkGeq(d, p.mkLiteral(100)));

		p.addAssertion(p.mkOr(p.mkNot(r), s));
		System.out.println(p.checkSat(true));

		System.out.println("c = " + p.evaluate(c));
		System.out.println("r = " + p.evaluate(r));

		p.push();

		p.addAssertion(p.mkOr(p.mkNot(s), p.mkLeq(c, p.mkLiteral(-100))));
		System.out.println(p.checkSat(true));

		p.pop();
		System.out.println(p.checkSat(true));

		// //////////////////////////////////////////////////////////////////////////

		p.push();

		final ProverFun f = p.mkUnintFunction("f",
				new ProverType[] { p.getIntType() }, p.getIntType());
		p.addAssertion(p.mkEq(f.mkExpr(new ProverExpr[] { c }), p.mkLiteral(5)));
		p.addAssertion(p.mkEq(f.mkExpr(new ProverExpr[] { d }), p.mkLiteral(6)));

		System.out.println(p.checkSat(true));

		System.out.println("f(c) = "
				+ p.evaluate(f.mkExpr(new ProverExpr[] { c })));
		p.addAssertion(p.mkEq(c, d));

		System.out.println(p.checkSat(true));

		p.pop();

		// //////////////////////////////////////////////////////////////////////////

		{
			p.push();

			final ProverExpr a = p.mkVariable("a", p.getIntType());
			final ProverExpr b = p.mkVariable("b", p.getIntType());

			final ProverFun geInt = p.mkDefinedFunction(
					"geInt",
					new ProverType[] { p.getIntType(), p.getIntType() },
					p.mkIte(p.mkGeq(p.mkBoundVariable(0, p.getIntType()),
							p.mkBoundVariable(1, p.getIntType())),
							p.mkLiteral(1), p.mkLiteral(0)));

			p.addAssertion(p.mkEq(geInt.mkExpr(new ProverExpr[] { a, b }),
					p.mkLiteral(1)));
			p.addAssertion(p.mkEq(geInt.mkExpr(new ProverExpr[] { b, a }),
					p.mkLiteral(1)));

			System.out.println(p.checkSat(true));

			p.addAssertion(p.mkNot(p.mkEq(a, b)));

			System.out.println(p.checkSat(true));

			p.pop();
		}

		// //////////////////////////////////////////////////////////////////////////

		System.out.println(p.checkSat(false));
		ProverResult res;
		while ((res = p.getResult(false)) == ProverResult.Running) {
			System.out.println("Running ... ");
			try {
				Thread.sleep(1);
			} catch (InterruptedException e) {
			}
		}

		System.out.println(res);

		System.out.println(p.checkSat(false));
		try {
			Thread.sleep(3);
		} catch (InterruptedException e) {
		}
		System.out.println(p.stop());

		System.out.println(p.checkSat(false));
		try {
			Thread.sleep(30);
		} catch (InterruptedException e) {
		}
		System.out.println(p.stop());

		// //////////////////////////////////////////////////////////////////////////

		p.reset();

		{
			p.setConstructProofs(true);
			final ProverExpr a = p.mkVariable("a", p.getIntType());
			final ProverExpr b = p.mkVariable("b", p.getIntType());

			p.setPartitionNumber(0);
			p.addAssertion(p.mkEq(
					p.mkStore(a, new ProverExpr[] { p.mkLiteral(0) },
							p.mkLiteral(1)), b));
			p.setPartitionNumber(1);
			p.addAssertion(p.mkEq(
					p.mkSelect(b, new ProverExpr[] { p.mkLiteral(0) }),
					p.mkLiteral(2)));

			System.out.println(p.checkSat(true));

			System.out.println(p.interpolate(new int[][] { new int[] { 0 },
					new int[] { 1 } })[0]);
		}

		p.shutdown();

	}

}
