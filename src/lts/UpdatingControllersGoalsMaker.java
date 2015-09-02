package lts;

import control.ControllerGoalDefinition;
import controller.game.util.GeneralConstants;
import lts.ltl.AssertDefinition;
import lts.ltl.FormulaSyntax;
import updatingControllers.UpdateConstants;

public class UpdatingControllersGoalsMaker {

	public static void addWeakUntilUpdatingGoal(Symbol formulaName, ControllerGoalDefinition cgd) {
		// getting elements that I need to build the formula
		Symbol weak = new Symbol(Symbol.WEAKUNTIL);
		ActionName stopOldSpecActionName = new ActionName(new Symbol(123, UpdateConstants.STOP_OLD_SPEC));
		FormulaSyntax stopOldSpecFormula = FormulaSyntax.make(stopOldSpecActionName);
		FormulaSyntax originalFormula = obtainFormula(formulaName);
		// building formula
		FormulaSyntax finalFormula = FormulaSyntax.make(originalFormula, weak, stopOldSpecFormula);
		// saving formula
		addFormula(cgd, formulaName.toString(), finalFormula, UpdateConstants.OLD_SUFFIX);
	}

	public static void addImplyUpdatingGoal(Symbol formulaName, ControllerGoalDefinition cgd) {
		// getting elements that I need to build the formula
		Symbol arrow = new Symbol(Symbol.ARROW);
		Symbol always = new Symbol(Symbol.ALWAYS);
		ActionName startNewSpecActionName = new ActionName(new Symbol(123, UpdateConstants.START_NEW_SPEC));
		FormulaSyntax startNewSpecFormula = FormulaSyntax.make(startNewSpecActionName);
		FormulaSyntax originalFormula = obtainFormula(formulaName);
		// building formula
		FormulaSyntax alwaysNewGoal = FormulaSyntax.make(null, always, originalFormula);
		FormulaSyntax implicationFormula = FormulaSyntax.make(startNewSpecFormula, arrow, alwaysNewGoal);
		FormulaSyntax finalFormula = FormulaSyntax.make(null, always, implicationFormula);
		// saving formula
		addFormula(cgd, formulaName.toString(), finalFormula, UpdateConstants.NEW_SUFFIX);
	}

	public static void addDontDoTwiceGoal(ControllerGoalDefinition cgd, String action, String formulaName) {

		Symbol arrow = new Symbol(Symbol.ARROW);
		Symbol always = new Symbol(Symbol.ALWAYS);
		Symbol next = new Symbol(Symbol.NEXTTIME);
		Symbol not = new Symbol(Symbol.PLING);
		ActionName actionName = new ActionName(new Symbol(123, action));
		FormulaSyntax formula = FormulaSyntax.make(actionName);

		FormulaSyntax dontDo = FormulaSyntax.make(null, not, formula);
		FormulaSyntax nextDontDo = FormulaSyntax.make(null, next, dontDo);
		FormulaSyntax implicationFormula = FormulaSyntax.make(formula, arrow, nextDontDo);
		FormulaSyntax finalFormula = FormulaSyntax.make(null, always, implicationFormula);

		// saving formula
		addFormula(cgd, formulaName, finalFormula, GeneralConstants.EMPTY_STRING);
	}

	/**
	 * @param formulaName
	 * @return
	 */
	private static FormulaSyntax obtainFormula(Symbol formulaName) {
		//TODO: Also consider that instead of a formula we could get a machine / lts
		AssertDefinition def = AssertDefinition.getConstraint(formulaName.getName());
		if (def == null) {
			throw new RuntimeException("ltl_property " + formulaName + " not found");
		}
		return def.getLTLFormula().removeLeftTemporalOperators();
	}

	private static void addFormula(ControllerGoalDefinition cgd, String name, FormulaSyntax formula, String suffix) {
		Symbol finalFormulaName = new Symbol(123, name + suffix);
		if (AssertDefinition.getConstraint(finalFormulaName.toString()) == null) {
			//TODO display a warning about possible duplicate property
			AssertDefinition.put(finalFormulaName, formula, null, null, null, true, false);
		}
		cgd.addSafetyDefinition(finalFormulaName);
	}
}