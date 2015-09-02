package updatingControllers.synthesis;

import ac.ic.doc.commons.relations.Pair;
import ac.ic.doc.mtstools.model.MTS;
import ac.ic.doc.mtstools.model.MTS.TransitionType;
import ac.ic.doc.mtstools.model.impl.MTSImpl;
import ac.ic.doc.mtstools.util.fsp.AutomataToMTSConverter;
import ac.ic.doc.mtstools.util.fsp.MTSToAutomataConverter;
import ar.dc.uba.model.condition.Fluent;
import ar.dc.uba.model.condition.FluentUtils;
import control.util.ControllerUtils;
import controller.game.util.FluentStateValuation;
import dispatcher.TransitionSystemDispatcher;
import lts.CompactState;
import lts.LTSOutput;
import updatingControllers.UpdateConstants;
import updatingControllers.structures.MappingStructure;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

public class UpdatingEnvironmentGenerator {

	private MTS<Pair<Long, Long>, String> oldPart;
	private MTS<Long, String> oldController;
	private MTS<Long, String> oldEnvironment;
	private MTS<Long, String> newEnvironment;
	private MTS<Long, String> machine;
	private MTS<Long, String> minimized;
	private Long lastState;
	private Set<Long> eParallelCStates; // used for relabeling actions
	private Set<Long> oldEnvironmentStates;

	public UpdatingEnvironmentGenerator(MTS<Long, String> oldController, MTS<Long, String> oldEnvironment, MTS<Long,
		String> newEnvironment) {

		this.oldController = oldController;
		this.oldEnvironment = oldEnvironment;
		this.newEnvironment = newEnvironment;

		machine = new MTSImpl<Long, String>(new Long(0));
		minimized = null;
		Pair<Long, Long> initialState = new Pair<Long, Long>(new Long(0), new Long(0));
		oldPart = new MTSImpl<Pair<Long, Long>, String>(initialState);

		lastState = new Long(0);

		eParallelCStates = new HashSet<Long>();
		oldEnvironmentStates = new HashSet<Long>();
	}

	//TODO make this static and remove constructor and properties
	public MTS<Long, String> generateEnvironment(Set<String> controllableActions, ArrayList<Pair<Fluent, Fluent>>
		mapping, LTSOutput output) {
		this.generateOldPart();
		this.completeWithOldEnvironment();
		this.changePairsToLong();
		MappingStructure mappingStructure = new MappingStructure(mapping);
		this.removeTopStates(mappingStructure);
		mappingStructure.buildValuation(machine, newEnvironment);
		HashMap<Long, Long> newEnvToThis = this.linkStatesWithSameFluentValues(mappingStructure.getStructureOld(),
			mappingStructure.getStructureNew());
		this.completeWithNewEnvironment(newEnvToThis);
		this.makeOldActionsUncontrollable(controllableActions);
		this.minimize(output);
		return minimized;
	}

	private void generateOldPart() {

		oldPart.addAction(UpdateConstants.BEGIN_UPDATE);

		// add beginUpdate transition and the new state from (0,0)
		addBeginUpdateTransition(oldPart.getInitialState());

		// BFS
		Queue<Pair<Long, Long>> toVisit = new LinkedList<Pair<Long, Long>>();
		Pair<Long, Long> firstState = new Pair<Long, Long>(oldController.getInitialState(), oldEnvironment
			.getInitialState());
		toVisit.add(firstState);
		ArrayList<Pair<Long, Long>> discovered = new ArrayList<Pair<Long, Long>>();

		while (!toVisit.isEmpty()) {
			Pair<Long, Long> actual = toVisit.remove();
			if (!discovered.contains(actual)) {
				discovered.add(actual);
				for (Pair<String, Long> action_toState : oldController.getTransitions(actual.getFirst(), MTS
					.TransitionType.REQUIRED)) {
					toVisit.addAll(nextToVisitInParallelComposition(actual, action_toState));
				}
			}
		}
	}

	private ArrayList<Pair<Long, Long>> nextToVisitInParallelComposition(Pair<Long, Long> actual, Pair<String, Long>
		transition) {

		ArrayList<Pair<Long, Long>> toVisit = new ArrayList<Pair<Long, Long>>();

		for (Pair<String, Long> action_toStateEnvironment : oldEnvironment.getTransitions(actual.getSecond(), MTS
			.TransitionType.REQUIRED)) {

			String action = action_toStateEnvironment.getFirst();
			Long toState = action_toStateEnvironment.getSecond();

			if (transition.getFirst().equals(action)) {

				//				action = action.concat(UpdateControllerSolver.label); // rename the actions so as to
				// distinguish from the controllable in the new problem controller
				oldPart.addAction(action); // actions is a Set. it Avoids duplicated actions
				Pair<Long, Long> newState = new Pair<Long, Long>(transition.getSecond(), toState);
				oldPart.addState(newState);

				addBeginUpdateTransition(newState);
				oldPart.addRequired(new Pair<Long, Long>(actual.getFirst(), actual.getSecond()), action, newState);
				toVisit.add(new Pair<Long, Long>(transition.getSecond(), toState));
			}
		}

		return toVisit;
	}

	private void addBeginUpdateTransition(Pair<Long, Long> newState) {

		oldPart.addState(new Pair<Long, Long>(new Long(-1), newState.getSecond()));
		oldPart.addRequired(newState, UpdateConstants.BEGIN_UPDATE, new Pair<Long, Long>(new Long(-1), newState
			.getSecond()));
	}

	private void completeWithOldEnvironment() {

		for (Long state : oldEnvironment.getStates()) {

			for (Pair<String, Long> action_toState : oldEnvironment.getTransitions(state, TransitionType.REQUIRED)) {

				String action = action_toState.getFirst();
				Long toState = action_toState.getSecond();
				Pair<Long, Long> newState = new Pair<Long, Long>(new Long(-1), toState);
				oldPart.addState(newState);
				oldPart.addAction(action);
				Pair<Long, Long> currentState = new Pair<Long, Long>(new Long(-1), state);
				oldPart.addRequired(currentState, action, newState);
			}
		}
	}

	private void changePairsToLong() {

		Map<Pair<Long, Long>, Long> visited = new HashMap<Pair<Long, Long>, Long>();

		// set first the state (0,0) to 0
		Pair<Long, Long> initialPair = new Pair<Long, Long>(new Long(0), new Long(0));
		Long initialState = this.getState(visited, initialPair);
		this.copyActions(visited, initialState, initialPair);

		for (Pair<Long, Long> pairState : oldPart.getStates()) {

			Long from = this.getState(visited, pairState);
			this.copyActions(visited, from, pairState);
		}
	}

	private Long getState(Map<Pair<Long, Long>, Long> visited, Pair<Long, Long> pairState) {
		Long state = null;
		if (visited.containsKey(pairState)) {
			state = visited.get(pairState);
		} else {
			visited.put(pairState, lastState);
			state = lastState;
			machine.addState(state);
			lastState++;
		}
		return state;
	}

	private void copyActions(Map<Pair<Long, Long>, Long> visited, Long longState, Pair<Long, Long> pairState) {

		for (Pair<String, Pair<Long, Long>> action_toState : oldPart.getTransitions(pairState, TransitionType
			.REQUIRED)) {

			String action = action_toState.getFirst();
			Pair<Long, Long> toPairState = action_toState.getSecond();
			machine.addAction(action);

			Long to = getState(visited, toPairState);
			machine.addRequired(longState, action, to);
		}
	}

	private void removeTopStates(MappingStructure mapping) {

		machine = ControllerUtils.removeTopStates(machine, mapping.getOldFluents());
		newEnvironment = ControllerUtils.removeTopStates(newEnvironment, mapping.getNewFluents());

		lastState = new Long(machine.getStates().size());
	}

	private HashMap<Long, Long> linkStatesWithSameFluentValues(HashMap<ArrayList<Boolean>, Set<Long>> structureOld,
															   HashMap<ArrayList<Boolean>, Set<Long>> structureNew) {

		setStatesForEachPart();

		machine.addAction(UpdateConstants.RECONFIGURE);

		HashMap<Long, Long> newEnvToUpdEnv = new HashMap<Long, Long>();

		for (ArrayList<Boolean> key : structureOld.keySet()) {
			for (Long oldEnvState : structureOld.get(key)) {
				//Build a no deterministic MTS
				if (structureNew.containsKey(key) && oldEnvironmentStates.contains(oldEnvState)) {
					for (Long newEnvironmentState : structureNew.get(key)) {

						if (newEnvToUpdEnv.containsKey(newEnvironmentState)) {
							Long toState = newEnvToUpdEnv.get(newEnvironmentState);
							machine.addRequired(oldEnvState, UpdateConstants.RECONFIGURE, toState);
						} else {
							Long newState = new Long(lastState);
							machine.addState(newState);
							machine.addRequired(oldEnvState, UpdateConstants.RECONFIGURE, newState);

							newEnvToUpdEnv.put(newEnvironmentState, newState);
							lastState++;
						}
					}
				}
			}
		}
		return newEnvToUpdEnv;
	}

	private void setStatesForEachPart() {

		Fluent afterBeginUpdateFluent = UpdatingControllerHandler.createOnlyTurnOnFluent(UpdateConstants.BEGIN_UPDATE);
		Set<Fluent> fluentSet = new HashSet<Fluent>();
		fluentSet.add(afterBeginUpdateFluent);

		FluentStateValuation<Long> valuationAfterBeginUpdate = FluentUtils.getInstance().buildValuation(machine,
			fluentSet);

		for (Long state : machine.getStates()) {
			if (valuationAfterBeginUpdate.isTrue(state, afterBeginUpdateFluent)) {
				addStopOldAndStartNewSpecActions(state);
				oldEnvironmentStates.add(state);
			} else {
				eParallelCStates.add(state);
			}
		}
	}

	private void addStopOldAndStartNewSpecActions(Long state) {
		machine.addAction(UpdateConstants.STOP_OLD_SPEC);
		machine.addAction(UpdateConstants.START_NEW_SPEC);
		machine.addRequired(state, UpdateConstants.STOP_OLD_SPEC, state);
		machine.addRequired(state, UpdateConstants.START_NEW_SPEC, state);
	}

	private void completeWithNewEnvironment(HashMap<Long, Long> newEnvToUpdEnv) {

		for (Long state : newEnvironment.getStates()) {

			for (Pair<String, Long> action_toState : newEnvironment.getTransitions(state, MTS.TransitionType
				.REQUIRED)) {

				if (newEnvToUpdEnv.containsKey(state)) {

					Long updEnvState = newEnvToUpdEnv.get(state);
					addTransitionCreatingNewStates(action_toState, updEnvState, newEnvToUpdEnv);
					addStopOldAndStartNewSpecActions(updEnvState);
				} else {

					Long updEnvState = addState(state, newEnvToUpdEnv);
					addTransitionCreatingNewStates(action_toState, updEnvState, newEnvToUpdEnv);
					addStopOldAndStartNewSpecActions(updEnvState);
				}
			}
		}
	}

	private void addTransitionCreatingNewStates(Pair<String, Long> action_toState, Long state, HashMap<Long, Long>
		newEnvToUpdEnv) {

		machine.addAction(action_toState.getFirst());
		if (!newEnvToUpdEnv.containsKey(action_toState.getSecond())) {

			Long newState = addState(action_toState.getSecond(), newEnvToUpdEnv);
			machine.addRequired(state, action_toState.getFirst(), newState);
		} else {
			machine.addRequired(state, action_toState.getFirst(), newEnvToUpdEnv.get(action_toState.getSecond()));
		}
	}

	private Long addState(Long originalState, HashMap<Long, Long> newEnvToUpdEnv) {

		Long newState = new Long(lastState);
		machine.addState(newState);
		newEnvToUpdEnv.put(originalState, newState);
		lastState++;
		return newState;
	}

	private void makeOldActionsUncontrollable(Set<String> controllableActions) {
		for (Long state : eParallelCStates) {
			List<Pair<String, Long>> toBeChanged = new ArrayList<Pair<String, Long>>();
			for (Pair<String, Long> action_toState : machine.getTransitions(state, TransitionType.REQUIRED)) {
				if (controllableActions.contains(action_toState.getFirst())) {
					toBeChanged.add(action_toState);
				}
			}
			for (Pair<String, Long> action_toState : toBeChanged) {
				String action = action_toState.getFirst();
				Long toState = action_toState.getSecond();
				machine.removeRequired(state, action, toState);
				String actionWithOld = action + UpdateConstants.OLD_LABEL;
				machine.addAction(actionWithOld);
				machine.addRequired(state, actionWithOld, toState);
			}
		}
		// add all .old accions to MTS so as to avoid problems while parallel composition
		for (String action : controllableActions) {
			if (UpdatingControllersUtils.isNotUpdateAction(action)) {
				machine.addAction(action + UpdateConstants.OLD_LABEL);
			}
		}
	}

	private void minimize(LTSOutput output) {
		CompactState csMachine = MTSToAutomataConverter.getInstance().convert(machine, "UPD_CONT_ENVIRONMENT", false);
		csMachine = TransitionSystemDispatcher.minimise(csMachine, output);
		this.minimized = AutomataToMTSConverter.getInstance().convert(csMachine);
	}
}