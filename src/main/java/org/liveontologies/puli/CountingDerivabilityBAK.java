package org.liveontologies.puli;

/*-
 * #%L
 * Proof Utility Library
 * $Id:$
 * $HeadURL:$
 * %%
 * Copyright (C) 2014 - 2023 Live Ontologies Project
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class CountingDerivabilityBAK<A, I extends AxiomPinpointingInference<?, ? extends A>>
		implements IncrementalDerivabilityChecker<A, I>, Predicate<I> {

	// logger for this class
		private static final Logger LOGGER_ = LoggerFactory
				.getLogger(CountingDerivabilityBAK.class);
	
	private final Proof<? extends I> proof_;

	private final Set<Object> unfolded_ = new HashSet<>();

	private final IdProvider<Object> conclusionIds_;
	private final IdProvider<A> axiomIds_;
	private final IdProvider<I> inferenceIds_;

	private static final int INITIAL_ARRY_SIZE_ = 128;

	/**
	 * Stores for each conclusion the list of all inferences in which this
	 * conclusion appears in the premise; the length of the list is stored as
	 * the first element of the array
	 */
	private int[][] inferencesByPremise_ = new int[INITIAL_ARRY_SIZE_][];

	/**
	 * Stores for each conclusion the list of inferences deriving this
	 * conclusion; the length of the list is stored as the first element of the
	 * array
	 */
	private int[][] inferencesByConclusion_ = new int[INITIAL_ARRY_SIZE_][];

	/**
	 * Stores for each inference its conclusion
	 */
	private int[] conclusionByInference_ = new int[INITIAL_ARRY_SIZE_];
	/**
	 * Stores for each inference the number of premises that need to be derived
	 * for inference to apply; so 0 means that all premises of the inference
	 * have been derived; a special case -1 means that the conclusion of this
	 * inference has been derived by this inference for the first time
	 */
	private int[] premisesRemained_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * Stores for each conclusion the number of inferences that derived it
	 */
	private int[] derivationCount_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * Axiom change index: for each axiom: 1 -added, -1 -removed, 0 -unchanged
	 */
	private int[] axiomChanges_ = new int[INITIAL_ARRY_SIZE_];
	/**
	 * The list of axioms pending for addition
	 */
	private int[] toAddAxioms_ = new int[INITIAL_ARRY_SIZE_];
	private int toAddAxiomsSize_ = 0;
	/**
	 * The list of axioms pending for removal
	 */
	private int[] toRemoveAxioms_ = new int[INITIAL_ARRY_SIZE_];
	private int removedAxiomsSize_ = 0;
	/**
	 * Conclusions to be processed
	 */
	private int[] todoConclusions_ = new int[INITIAL_ARRY_SIZE_];
	private int todoConclusionsSize_ = 0;
	/**
	 * Counts the number of over-deleted conclusions that cannot be re-derived
	 */
	private int completelyOverDeleted_ = 0;

	// statistic
	private int addCount_ = 0, overdeleteCount_ = 0, rederiveCheckedCount_ = 0,
			rederiveRemainCount_ = 0;

	public CountingDerivabilityBAK(Proof<? extends I> proof) {
		IdSupplier conclusionAndAxiomIdSupplier = new IdSupplier();
		IdSupplier inferenceIdSupplier = new IdSupplier();
		this.proof_ = proof;
		// ensure that conclusions and axioms have different IDs by using the
		// same supplier
		this.conclusionIds_ = new IdProvider<>(conclusionAndAxiomIdSupplier);
		this.axiomIds_ = new IdProvider<>(conclusionAndAxiomIdSupplier);
		this.inferenceIds_ = new IdProvider<>(inferenceIdSupplier);
	}

	@Override
	public Proof<? extends I> getProof() {
		return this.proof_;
	}

	@Override
	public boolean test(I inf) {
		assert todoConclusionsSize_ == 0;
		int infId = inferenceIds_.getId(inf);
		if (getValue(conclusionByInference_, infId - 1) != 0) {
			// inference already indexed
			return true;
		}
		int cId = conclusionIds_.getId(inf.getConclusion());
		List<?> premises = inf.getPremises();
		Set<? extends A> justification = inf.getJustification();
		int rem = premises.size() + justification.size();
		LOGGER_.trace("Inference {}: {} -|", infId, cId);
		for (A axiom : justification) {
			int axiomId = axiomIds_.getId(axiom);
			inferencesByPremise_ = addValue(inferencesByPremise_, axiomId - 1,
					infId);
			LOGGER_.trace("                  | {}", axiomId);
			if (isDerivedId(axiomId)) {
				rem--;
			}
		}
		for (Object premise : premises) {
			int premiseId = conclusionIds_.getId(premise);
			inferencesByPremise_ = addValue(inferencesByPremise_, premiseId - 1,
					infId);
			LOGGER_.trace("                  | {}", premiseId);
			if (isDerivedId(premiseId)) {
				rem--;
			}
		}
		conclusionByInference_ = setValue(conclusionByInference_, infId - 1,
				cId);
		inferencesByConclusion_ = addValue(inferencesByConclusion_, cId - 1,
				infId);
		if (rem == 0 && add(cId)) {
			rem = -1;
			propagateAdditions();
		}
		setPremisesRemained(infId, rem);
		return true;
	}

	@Override
	public boolean addAxiom(A axiom) {
		int axId = axiomIds_.getId(axiom);
		if (getDerivationCount(axId) + getAxiomDelta(axId) == 0) {
			LOGGER_.trace("Add: {}", axId);
			incrementAxiomDelta(axId, 1);
			toAddAxioms_ = setValue(toAddAxioms_, toAddAxiomsSize_++, axId);
			return true;
		}
		// else already added
		LOGGER_.trace("Add: {} (ignored)", axId);
		return false;
	}

	@Override
	public boolean removeAxiom(A axiom) {
		int axId = axiomIds_.getId(axiom);
		if (getDerivationCount(axId) + getAxiomDelta(axId) > 0) {
			LOGGER_.trace("Remove: {}", axId);
			incrementAxiomDelta(axId, -1);
			toRemoveAxioms_ = setValue(toRemoveAxioms_, removedAxiomsSize_++,
					axId);
			return true;
		}
		// else not added
		LOGGER_.trace("Remove: {} (ignored)", axId);
		return false;
	}

	public boolean isDerivedId(int cId) {
		return getDerivationCount(cId) > 0;
	}

	@Override
	public boolean isDerivable(Object conclusion) {
		loadDeletions();
		propagateDeletions();
		rederive();
		propagateAdditions();
		Proofs.unfoldRecursively(proof_, conclusion, this, unfolded_);
		loadAdditions();
		propagateAdditions();
		return isDerivedId(conclusionIds_.getId(conclusion));
	}

	@Override
	public Proof<I> explainIsDerivable(Object conclusion) {
		if (!isDerivable(conclusion)) {
			return null;
		}
		// else construct proof of fired inferences
		return new Proof<I>() {

			@Override
			public Collection<? extends I> getInferences(Object conclusion) {
				int cId = conclusionIds_.getId(conclusion);
				int[] inferences = getValue(inferencesByConclusion_, cId - 1);
				if (inferences == null) {
					return Collections.emptySet();
				}
				for (int i = 1; i <= inferences[0]; i++) {
					int infId = inferences[i];
					if (getPremisesRemained(infId) == -1) {
						// the first inference that derived the conclusion
						I inf = inferenceIds_.getValue(infId);
						return Collections.singleton(inf);
					}
				}
				return Collections.emptySet();
			}
		};
	}

	private void loadAdditions() {
		while (toAddAxiomsSize_ > 0) {
			int cId = toAddAxioms_[--toAddAxiomsSize_];
			if (axiomChanges_[cId - 1] > 0) {
				axiomChanges_[cId - 1] = 0;
				add(cId);
			} else {
				LOGGER_.trace("{}: no need to load", cId);
			}
		}
	}

	private void loadDeletions() {
		while (removedAxiomsSize_ > 0) {
			int cId = toRemoveAxioms_[--removedAxiomsSize_];
			if (axiomChanges_[cId - 1] < 0) {
				axiomChanges_[cId - 1] = 0;
				delete(cId, true);
			} else {
				LOGGER_.trace("{}: no need to overdelete", cId);
			}
		}
	}

	private boolean add(int cId) {
		LOGGER_.trace("Derived: {}", cId);
		boolean added = false;
		int count = getDerivationCount(cId);
		if (count++ == 0) {
			todo(cId);
			added = true;
		}
		setDerivationCount(cId, count);
		return added;
	}

	private void delete(int cId, boolean overdelete) {
		int count = getDerivationCount(cId);
		assert count > 0;
		if (--count == 0) {
			completelyOverDeleted_++;
		}
		setDerivationCount(cId, count);
		if (overdelete) {
			todo(cId);
		}
	}

	private void propagateAdditions() {
		while (todoConclusionsSize_ > 0) {
			int cId = todoConclusions_[--todoConclusionsSize_];
			LOGGER_.trace("Propagating addition: {}", cId);
			addCount_++;
			int[] inferences = getValue(inferencesByPremise_, cId - 1);
			if (inferences == null) {
				continue;
			}
			for (int i = 1; i <= inferences[0]; i++) {
				countdown(inferences[i]);
			}
		}
	}

	private void propagateDeletions() {
		int propagated = 0;		
		while (propagated < todoConclusionsSize_) {
			int cId = todoConclusions_[propagated++];
			LOGGER_.trace("Propagating deletion: {}", cId);			 
			overdeleteCount_++;
			int[] inferences = getValue(inferencesByPremise_, cId - 1);
			if (inferences == null) {
				continue;
			}
			for (int i = 1; i <= inferences[0]; i++) {
				countup(inferences[i]);
			}
		}
		if (completelyOverDeleted_ == todoConclusionsSize_) {
			// nothing to re-derive
			todoConclusionsSize_ = 0;
		}
		completelyOverDeleted_ = 0;
	}

	private void countdown(int infId) {		
		int rem = getPremisesRemained(infId);
		LOGGER_.trace("Countdown inference {} for {}", infId, rem);
		assert rem > 0;		
		if (--rem == 0) {
			int cId = conclusionByInference_[infId - 1];
			if (add(cId)) {
				LOGGER_.trace("{} added by inference {}", cId, infId);
				rem = -1;
			}
		}
		setPremisesRemained(infId, rem);
	}

	private void countup(int infId) {
		int cId = conclusionByInference_[infId - 1];
		int rem = getPremisesRemained(infId);
		LOGGER_.trace("Countup inference {} for {}", infId, rem);
		if (rem == -1) {
			rem = 1;
			LOGGER_.trace("{} overdeleted by inference {}", cId, infId);
			delete(cId, true);
		} else if (rem++ == 0) {
			delete(cId, false);
		}
		setPremisesRemained(infId, rem);
	}

	private void rederive() {
		int overdeleted = 0, rederived = 0;
		while (overdeleted < todoConclusionsSize_) {
			int cId = todoConclusions_[overdeleted++];
			rederiveCheckedCount_++;
			if (isDerivedId(cId)) {
				rederiveRemainCount_++;
				int[] inferences = getValue(inferencesByConclusion_, cId - 1);
				for (int i = 1; i <= inferences[0]; i++) {
					int infId = inferences[i];
					if (getPremisesRemained(infId) == 0) {
						LOGGER_.trace("{} rederived by inference {}", cId, infId);
						setPremisesRemained(infId, -1);
						break;
					}
				}
				todoConclusions_[rederived++] = cId;
			}
		}
		todoConclusionsSize_ = rederived;
	}

	private void todo(int cId) {
		todoConclusions_ = setValue(todoConclusions_, todoConclusionsSize_++,
				cId);
	}

	private int getDerivationCount(int cId) {
		return getValue(derivationCount_, cId - 1);
	}

	private void setDerivationCount(int cId, int value) {
		LOGGER_.trace("{} set derivations: {}", cId, value);
		derivationCount_ = setValue(derivationCount_, cId - 1, value);
	}

	private int getPremisesRemained(int infId) {
		int remained = getValue(premisesRemained_, infId - 1);
		LOGGER_.trace("Inference {} current premises remained: {}", infId,
				remained);
		return remained;
	}

	private void setPremisesRemained(int infId, int value) {
		LOGGER_.trace("Inference {} remain to fire: {}", infId, value);
		premisesRemained_ = setValue(premisesRemained_, infId - 1, value);
	}

	private int getAxiomDelta(int axId) {
		return getValue(axiomChanges_, axId - 1);
	}

	private void incrementAxiomDelta(int axId, int delta) {
		while (axId > axiomChanges_.length) {
			axiomChanges_ = resize(axiomChanges_);
		}
		axiomChanges_[axId - 1] += delta;
	}

	private static int getValue(int[] array, int pos) {
		assert pos >= 0 : pos;
		return pos < array.length ? array[pos] : 0;
	}

	private static int[] getValue(int[][] array, int pos) {
		assert pos >= 0 : pos;
		return pos < array.length ? array[pos] : null;
	}

	private static int[] setValue(int[] array, int pos, int value) {
		assert pos >= 0 : pos;
		while (pos >= array.length) {
			array = resize(array);
		}
		array[pos] = value;
		return array;
	}

	private static int[][] addValue(int[][] table, int pos, int value) {
		assert pos >= 0 : pos;
		while (pos >= table.length) {
			table = resize(table);
		}
		int[] values = table[pos];
		if (values == null) {
			values = new int[8];
			table[pos] = values;
		}
		int size = ++values[0];
		if (size == values.length) {
			values = resize(values);
			table[pos] = values;
		}
		values[size] = value;
		return table;
	}

	// private static int getCompressedValue(int[] array, int id) {
	// assert id >= 0 : id;
	// int pos = id >>> 3;
	// if (pos >= array.length) {
	// return 0;
	// }
	// int v = array[pos];
	// // printValue(id, v);
	// int shift = (id & 7) * 4;
	// return (v >>> shift) & 15;
	// }
	//
	// private static int[] setCompressedValue(int[] array, int id, int value) {
	// assert id >= 0 : id;
	// assert value >= 0 && value < 16 : value;
	// int pos = id >>> 3;
	// while (pos >= array.length) {
	// array = resize(array);
	// }
	// int v = array[pos];
	// int shift = (id & 7) * 4;
	// v &= ~(15 << shift);
	// v |= value << shift;
	// array[pos] = v;
	// return array;
	// }

	private static int[] resize(int[] values) {
		return Arrays.copyOf(values, 2 * values.length);
	}

	private static int[][] resize(int[][] values) {
		return Arrays.copyOf(values, 2 * values.length);
	}

}
