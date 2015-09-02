package lts;

import ac.ic.doc.commons.relations.Pair;
import ar.dc.uba.model.condition.Fluent;
import control.ControllerGoalDefinition;
import controller.model.gr.GRControllerGoal;
import lts.ltl.AssertDefinition;
import lts.ltl.PredicateDefinition;
import updatingControllers.UpdateConstants;
import updatingControllers.structures.UpdatingControllerCompositeState;
import updatingControllers.synthesis.UpdatingControllersUtils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;
import java.util.Vector;

public class UpdatingControllersDefinition extends CompositionExpression {

	private Symbol oldController;
	private Symbol oldEnvironment;
	private Symbol newEnvironment;
	private Symbol oldGoal;
	private Symbol newGoal;
	private List<Symbol> safety;
	private Boolean nonblocking;
	private ArrayList<Pair<Symbol, Symbol>> updFluents;
	private Boolean debugMode;
	private ArrayList<Symbol> checkTrace;

	public UpdatingControllersDefinition(Symbol current) {
		super();
		super.setName(current);
		oldController = new Symbol();
		oldEnvironment = new Symbol();
		newEnvironment = new Symbol();
		safety = new ArrayList<Symbol>();
		nonblocking = false;
		updFluents = new ArrayList<Pair<Symbol, Symbol>>();
		debugMode = false;
		checkTrace = new ArrayList<Symbol>();
	}

	public Set<String> generateUpdatingControllableActions(ControllerGoalDefinition oldGoalDef,
	                                                       ControllerGoalDefinition newGoalDef) {
		Set<String> oldControllableActions = compileSet(oldGoalDef.getControllableActionSet());
		Set<String> newControllableActions = compileSet(newGoalDef.getControllableActionSet());
		Set<String> controllable = new HashSet<String>();
		controllable.addAll(oldControllableActions);
		controllable.addAll(newControllableActions);
		controllable.add(UpdateConstants.STOP_OLD_SPEC);
		controllable.add(UpdateConstants.START_NEW_SPEC);
		controllable.add(UpdateConstants.RECONFIGURE);
		return controllable;
	}

	@Override
	protected CompositeState compose(Vector<Value> actuals) {
		CompositionExpression oldController = LTSCompiler.getComposite(this.getOldController().toString());
		// may be change to processes.get(...)
		CompositeState oldC = oldController.compose(null);

		CompositionExpression oldEnvironment = LTSCompiler.getComposite(this.getOldEnvironment().toString());
		// may be change to processes.get(...)
		CompositeState oldE = oldEnvironment.compose(null);

		CompositionExpression newEnvironment = LTSCompiler.getComposite(this.getNewEnvironment().toString());
		// may be change to processes.get(...)
		CompositeState newE = newEnvironment.compose(null);

		// GOAL
		ControllerGoalDefinition oldGoalDef = ControllerGoalDefinition.getDefinition(this.getOldGoal());
		ControllerGoalDefinition newGoalDef = ControllerGoalDefinition.getDefinition(this.getNewGoal());
		Set<String> controllableSet = this.generateUpdatingControllableActions(oldGoalDef, newGoalDef);
		Symbol controllableSetSymbol = LTSCompiler.saveControllableSet(controllableSet, this.getName().getName());
		GRControllerGoal<String> grGoal = UpdatingControllersUtils.generateGRUpdateGoal(this, oldGoalDef, newGoalDef,
			controllableSet);
		ControllerGoalDefinition newGoal = UpdatingControllersUtils.generateSafetyGoalDef(this, oldGoalDef,
			newGoalDef, controllableSetSymbol, output);

		// MAPPING FLUENTS
		ArrayList<Pair<Fluent, Fluent>> fluents = UpdatingControllersUtils.compileFluents(this.getUpdFluents());

		// DEBUG
		Boolean debugMode = this.debugModelOn();
		ArrayList<String> checkTrace = UpdatingControllersUtils.compileCheckTraces(this.getCheckTrace());

		UpdatingControllerCompositeState ucce = new UpdatingControllerCompositeState(oldC, oldE, newE, newGoal,
			grGoal, fluents, debugMode, checkTrace, name.getName());
		return ucce;
	}


	private HashSet<String> compileSet(Symbol setSymbol) {
		Hashtable<?, ?> constants = LabelSet.getConstants();
		LabelSet labelSet = (LabelSet) constants.get(setSymbol.toString());
		if (labelSet == null) {
			Diagnostics.fatal("Set not defined.");
		}
		Vector<String> actions = labelSet.getActions(null);
		return new HashSet<String>(actions);
	}

	public void setOldController(ArrayList<Symbol> oldController) {
		this.oldController = oldController.get(0);
	}

	public void setOldEnvironment(ArrayList<Symbol> oldEnvironment) {
		this.oldEnvironment = oldEnvironment.get(0);
	}

	public void setNewEnvironment(ArrayList<Symbol> newEnvironment) {
		this.newEnvironment = newEnvironment.get(0);
	}

	public void addSafety(Symbol safety) {
		this.safety.add(safety);
	}

	public void setNonblocking() {
		this.nonblocking = true;
	}

	public void setUpdFluents(ArrayList<Pair<Symbol, Symbol>> updFluents) {
		this.updFluents = updFluents;
	}

	public void setDebugMode() {
		debugMode = true;
	}

	public void setCheckTrace(ArrayList<Symbol> traceToCheck) {
		checkTrace = traceToCheck;
	}

	public Symbol getOldController() {
		return oldController;
	}

	public Symbol getOldEnvironment() {
		return oldEnvironment;
	}

	public Symbol getNewEnvironment() {
		return newEnvironment;
	}

	public List<Symbol> getSafety() {
		return safety;
	}

	public Boolean isNonblocking() {
		return nonblocking;
	}

	public ArrayList<Pair<Symbol, Symbol>> getUpdFluents() {
		return updFluents;
	}

	public Boolean debugModelOn() {
		return debugMode;
	}

	public ArrayList<Symbol> getCheckTrace() {
		return checkTrace;
	}

	public Symbol getNewGoal() {
		return newGoal;
	}

	public void setNewGoal(Symbol newGoal) {
		this.newGoal = newGoal;
	}

	public Symbol getOldGoal() {
		return oldGoal;
	}

	public void setOldGoal(Symbol oldGoal) {
		this.oldGoal = oldGoal;
	}
}