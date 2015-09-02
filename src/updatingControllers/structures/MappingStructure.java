package updatingControllers.structures;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import ac.ic.doc.commons.relations.Pair;
import ac.ic.doc.mtstools.model.MTS;
import ar.dc.uba.model.condition.Fluent;
import ar.dc.uba.model.condition.FluentUtils;
import controller.game.util.FluentStateValuation;

public class MappingStructure {

	private ArrayList<Fluent> oldFluents;
	private ArrayList<Fluent> newFluents;
	private HashMap<ArrayList<Boolean>, Set<Long>> structureOld;
	private HashMap<ArrayList<Boolean>, Set<Long>> structureNew;

	public MappingStructure(ArrayList<Pair<Fluent, Fluent>> updFluents) {
		//we need them as List because order matters (these are used as the key of the structures above)
		oldFluents = new ArrayList<Fluent>();
		newFluents = new ArrayList<Fluent>();

		for (Pair<Fluent, Fluent> fluentsPair : updFluents) {
			oldFluents.add(fluentsPair.getFirst());
			newFluents.add(fluentsPair.getSecond());
		}
	}

	public void buildValuation(MTS<Long, String> updEnvironment, MTS<Long, String> newEnvironment) {

		Set<Fluent> fluentsOld = new HashSet<Fluent>(oldFluents);
		Set<Fluent> fluentsNew = new HashSet<Fluent>(newFluents);
		FluentUtils fluentUtils = FluentUtils.getInstance();
		FluentStateValuation<Long> valuationOld = fluentUtils.buildValuation(updEnvironment, fluentsOld);
		FluentStateValuation<Long> valuationNew = fluentUtils.buildValuation(newEnvironment, fluentsNew);

		structureOld = setStructure(updEnvironment, valuationOld, oldFluents);
		structureNew = setStructure(newEnvironment, valuationNew, newFluents);
	}

	private HashMap<ArrayList<Boolean>, Set<Long>> setStructure(MTS<Long, String> mts, FluentStateValuation<Long>
		valuation, ArrayList<Fluent> fluents) {
		HashMap<ArrayList<Boolean>, Set<Long>> structure = new HashMap<ArrayList<Boolean>, Set<Long>>();

		for (Long state : mts.getStates()) {

			ArrayList<Boolean> valuationOfState = valuation.getFluentsFromState(state, fluents);
			if (structure.containsKey(valuationOfState)) {
				Set<Long> value = structure.get(valuationOfState);
				value.add(state);
				structure.put(valuationOfState, value);
			} else {
				Set<Long> newList = new HashSet<Long>();
				newList.add(state);
				structure.put(valuationOfState, newList);
			}
		}
		return structure;
	}

	public ArrayList<Fluent> getOldFluents() {
		return oldFluents;
	}

	public ArrayList<Fluent> getNewFluents() {
		return newFluents;
	}

	public HashMap<ArrayList<Boolean>, Set<Long>> getStructureOld() {
		return structureOld;
	}

	public HashMap<ArrayList<Boolean>, Set<Long>> getStructureNew() {
		return structureNew;
	}
}