package updatingControllers.structures.graph;

import ac.ic.doc.commons.relations.Pair;
import ac.ic.doc.mtstools.model.impl.MarkedMTS;
import ar.dc.uba.model.condition.Fluent;

import java.util.ArrayList;
import java.util.Set;

/**
 * Created by Victor Wjugow on 27/05/15.
 */
public class UpdateTransition {

	private MarkedMTS<Long, String> updateController;
	private ArrayList<Pair<Fluent, Fluent>> fluents;
	private Set<String> controllableActions;

	public MarkedMTS<Long, String> getUpdateController() {
		return updateController;
	}

	public void setUpdateController(MarkedMTS<Long, String> updateController) {
		this.updateController = updateController;
	}

	public ArrayList<Pair<Fluent, Fluent>> getFluents() {
		return fluents;
	}

	public void setFluents(ArrayList<Pair<Fluent, Fluent>> fluents) {
		this.fluents = fluents;
	}

	public Set<String> getControllableActions() {
		return controllableActions;
	}

	public void setControllableActions(Set<String> controllableActions) {
		this.controllableActions = controllableActions;
	}
}