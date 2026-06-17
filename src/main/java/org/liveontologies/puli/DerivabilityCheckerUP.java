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
import java.util.function.Predicate;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * An {@link IncrementalDerivabilityChecker} that works by unit propagation.
 *
 * A unit is a conclusion or its negation that has been derived. Initially,
 * positive conclusions are derived as a result of added axioms by
 * {@link #addAxiom(Object)} and negative conclusion as a result of adding the
 * negation of the query checked by {@link #isDerivable(Object)}. New positive
 * or negative conclusions are propagated using the inferences of a
 * {@link Proof}: (1) if all premises of the inference are derived then its
 * conclusion is derived, and (2) if the negation of conclusion is derived and
 * all but one premises of the inference are derived then the negation of the
 * remaining premise is derived. If all premises and the negation of the
 * conclusion of some inference are derived then the clash is obtained, in which
 * case {@link #isDerivable(Object)} returns {@code true}. If the unit
 * propagation completes without deriving a clash, then
 * {@link #isDerivable(Object)} returns {@code false}.
 *
 * The derived negative and positive conclusions are incrementally updated after
 * calling {@link #addAxiom(Object)}, {@link #removeAxiom(Object)} and
 * {@link #isDerivable(Object)} for a different query using the standard
 * (over)delete-rederive (DRed) procedure (see, e.g.,
 * <a href="http://www.vldb.org/conf/1996/P075.PDF">Incremental Maintenance of
 * Externally Materialized Views</a>). To reduce the unnecessary over-deletion,
 * for each derived (negated) conclusion we store the inference using which it
 * was propagated and only delete this conclusion if this inference does not
 * apply after changes and propagated deletions.
 *
 *
 * @param <A>
 * @param <I>
 */
public class DerivabilityCheckerUP<A, I extends AxiomPinpointingInference<?, ? extends A>>
		implements IncrementalDerivabilityChecker<A, I>, Predicate<I> {

	// logger for this class
	private static final Logger LOGGER_ = LoggerFactory
			.getLogger(DerivabilityCheckerUP.class);

	/**
	 * The default initial size of created index arrays
	 */
	private static final int INITIAL_ARRY_SIZE_ = 128;

	/**
	 * The proof from which inferences are taken
	 */
	private final Proof<? extends I> proof_;

	/**
	 * The set conclusions which inferences are indexed to be used for unit
	 * propagation
	 */
	private final Set<Object> unfolded_ = new HashSet<>();

	/**
	 * Assignment of integer identifiers to conclusions
	 */
	private final IdProvider<Object> conclusionIds_;
	/**
	 * Assignment of integer identifiers to axioms
	 */
	private final IdProvider<A> axiomIds_;
	/**
	 * Assignment of integer identifiers to inferences
	 */
	private final IdProvider<I> inferenceIds_;

	/**
	 * Stores for each conclusion ID the array partially filled with IDs of
	 * inferences in which this conclusion appears in the premise; the length of
	 * the array is stored as the first element of the array
	 */
	private int[][] inferencesByPremise_ = new int[INITIAL_ARRY_SIZE_][];

	/**
	 * Stores for each axiom ID the array partially filled with IDs of
	 * inferences in which this axiom appears as justification; the length of
	 * the array is stored as the first element of the array
	 */
	private int[][] inferencesByAxiom_ = new int[INITIAL_ARRY_SIZE_][];

	/**
	 * Stores for each conclusion ID the array partially filled with IDs of
	 * inferences deriving this conclusion; the length of the list is stored as
	 * the first element of the array
	 */
	private int[][] inferencesByConclusion_ = new int[INITIAL_ARRY_SIZE_][];

	/**
	 * Stores for each inference ID its conclusion ID followed by negations of
	 * premises IDs
	 */
	private int[][] inferenceRecord_ = new int[INITIAL_ARRY_SIZE_][];
	/**
	 * The number of undecided parameters of inference. Initially, it is the
	 * number of premises plus justification axioms plus 1. Whenever an axiom is
	 * added, premise is derived, or the negation of conclusion is derived, this
	 * value is decreased by 1. If this value becomes 1, the inference can be
	 * used for the unit propagation of the remaining undecided parameter. If it
	 * becomes 0, the inference causes the clash.
	 */
	private int[] inferenceRemainToClash_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * Stores for each conclusion ID the inference ID using which it was
	 * derived, or 0 if it was not (positively) derived yet
	 */
	private int[] derivedByPositive_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * Stores for each conclusion ID the inference ID using which its negation
	 * was derived, or 0 if its negation was not derived yet
	 */
	private int[] derivedByNegative_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * The dynamic list of axiom IDs pending for addition
	 */
	private int[] toAddAxioms_ = new int[INITIAL_ARRY_SIZE_];
	private int toAddAxiomsSize_ = 0;
	/**
	 * The dynamic list of axiom IDs pending for removal
	 */
	private int[] toRemoveAxioms_ = new int[INITIAL_ARRY_SIZE_];
	private int toRemoveAxiomsSize_ = 0;
	/**
	 * The dynamic list of (positive or negative) conclusion IDs to be processed
	 */
	private int[] toPropagateConclusions_ = new int[INITIAL_ARRY_SIZE_];
	private int toPropagateConclusionsSize_ = 0;
	/**
	 * The dynamic list of IDs of inferences to be used for unit propagation
	 */
	private int[] toFireInferences_ = new int[INITIAL_ARRY_SIZE_];
	private int toFireInferencesSize_ = 0;
	/**
	 * The dynamic list of IDs of inferences that could be used for unit
	 * propagation but were found after the clash was derived
	 */
	private int[] unfiredInferences_ = new int[INITIAL_ARRY_SIZE_];
	private int unfiredInferencesSize_ = 0;

	/**
	 * The ID of the conclusion that was used last time for checking
	 * derivability {@link #isDerivable(Object)}
	 */
	private int previousQueryId_ = 0;

	/**
	 * The ID representing (trivial) inference that assumes to derive the
	 * initial (negated) conclusions (resulted from addition of axioms or
	 * negation of the query)
	 */
	private final int toldInferenceId_;

	public DerivabilityCheckerUP(Proof<? extends I> proof) {
		IdSupplier conclusionAndAxiomIdSupplier = new IdSupplier();
		IdSupplier inferenceIdSupplier = new IdSupplier();
		this.proof_ = proof;
		// ensure that all conclusions and axioms are assigned to unique IDs by
		// using the same supplier, inferences have a separate pool of IDs
		this.conclusionIds_ = new IdProvider<>(conclusionAndAxiomIdSupplier);
		this.axiomIds_ = new IdProvider<>(conclusionAndAxiomIdSupplier);
		this.inferenceIds_ = new IdProvider<>(inferenceIdSupplier);
		this.toldInferenceId_ = inferenceIdSupplier.getNextId();
	}

	@Override
	public Proof<? extends I> getProof() {
		// only use inferences whose all justifications were added
		return Proofs.filter(proof_, inf -> inf.getJustification()
				.parallelStream().allMatch(this::isUsed));
	}

	@Override
	public boolean addAxiom(A axiom) {
		int axId = axiomIds_.getId(axiom);
		if (!isDerivedId(axId)) {
			LOGGER_.trace("{}: added", axId);
			setIsDerivedBy(axId, toldInferenceId_);
			todo(axId);
			return true;
		} else {
			LOGGER_.trace("{}: already added before", axId);
			return false;
		}
	}

	@Override
	public boolean removeAxiom(A axiom) {
		int axId = axiomIds_.getId(axiom);
		if (isDerivedId(axId)) {
			LOGGER_.trace("{}: removed", axId);
			setIsDerivedBy(axId, 0);
			todo(-axId);
			return true;
		} else {
			LOGGER_.trace("{}: already removed before", axId);
			return false;
		}
	}

	@Override
	public boolean isDerivable(Object conclusion) {
		int cId = conclusionIds_.getId(conclusion);
		LOGGER_.trace("Index {} => {}", conclusion, cId);
		assert cId != 0 : cId;
		pruneChanges();
		if (cId != previousQueryId_ && previousQueryId_ != 0) {
			if (isDerivedId(-previousQueryId_)) {
				setIsDerivedBy(-previousQueryId_, 0);
				todo(-previousQueryId_);
			}
		}
		loadDeletions();
		propagateDeletions();
		rederive();
		Proofs.unfoldRecursively(proof_, conclusion, this, unfolded_);
		if (isDerivedId(cId)) {
			// marker for clash
			notFire(toldInferenceId_);
		} else if (cId != previousQueryId_) {
			setIsDerivedBy(-cId, toldInferenceId_);
			todo(-cId);
		}

		loadAdditions();
		propagateAdditions();
		previousQueryId_ = cId;
		boolean result = hasClash();
		LOGGER_.debug("isDerivable({}): {}", conclusion, result);
		return result;
	}

	@Override
	public boolean test(I inf) {
		// indexing the inference, always returns true
		assert toPropagateConclusionsSize_ == 0 : toPropagateConclusionsSize_;
		int infId = inferenceIds_.getId(inf);
		if (getList(inferenceRecord_, infId - 1)[0] > 0) {
			// inference already indexed
			return true;
		}
		LOGGER_.trace("Inference: {} => {}", inf, infId);
		Object conclusion = inf.getConclusion();
		int cId = conclusionIds_.getId(conclusion);
		LOGGER_.trace("Conclusion: {} => {}", conclusion, cId);
		List<?> premises = inf.getPremises();
		Set<? extends A> justification = inf.getJustification();
		int rem = premises.size() + justification.size() + 1;
		int[] infRecord = new int[premises.size() + 1];
		int i = 0; // index over infRecord
		infRecord[i++] = cId;
		if (isDerivedId(-cId)) {
			rem--;
		}
		for (A axiom : justification) {
			int axiomId = axiomIds_.getId(axiom);
			inferencesByAxiom_ = addValue(inferencesByAxiom_, axiomId - 1,
					infId);
			LOGGER_.trace("Axiom: {} => {}", axiom, axiomId);
			if (isDerivedId(axiomId)) {
				rem--;
			}
		}
		for (Object premise : premises) {
			int premiseId = conclusionIds_.getId(premise);
			inferencesByPremise_ = addValue(inferencesByPremise_, premiseId - 1,
					infId);
			infRecord[i++] = -premiseId;
			LOGGER_.trace("Premise: {} => {}", premise, premiseId);
			if (isDerivedId(premiseId)) {
				rem--;
			}
		}
		LOGGER_.debug("Inference {}: {}", infId, infRecord);
		inferencesByConclusion_ = addValue(inferencesByConclusion_, cId - 1,
				infId);
		inferenceRecord_ = setValue(inferenceRecord_, infId - 1, infRecord);
		setPremisesRemained(infId, rem);
		if (rem > 1) {
			return true;
		} else if (rem == 0 || hasClash()) {
			notFire(infId);
		} else {
			toFire(infId);
		}
		return true;
	}

	@Override
	public Proof<I> explainIsDerivable(Object conclusion) {
		// Ensure that derivability is checked
		isDerivable(conclusion);
		return new Proof<I>() {

			// copy derivations in case axioms are added or removed
			private final int[] derivedByPositiveCopy_ = Arrays
					.copyOf(derivedByPositive_, derivedByPositive_.length);

			{
				if (hasClash()) {
					// turn negative propagations into positive propagations
					assert previousQueryId_ != 0;
					int infId = unfiredInferences_[0]; // the inference caused
														// clash
					int cId;
					while (infId != toldInferenceId_) {
						int[] infRecord = inferenceRecord_[infId - 1];
						LOGGER_.trace("Reverting {}: {}", infId, infRecord);
						cId = infRecord[0];
						setValue(derivedByPositiveCopy_, cId - 1, infId);
						infId = getValue(derivedByNegative_, cId - 1);
						break;
					}
				}
			}

			@Override
			public Collection<? extends I> getInferences(Object conclusion) {
				int cId = conclusionIds_.getId(conclusion);
				int infId = getValue(derivedByPositiveCopy_, cId - 1);
				if (infId == 0) {
					// not derived
					return Collections.emptySet();
				}
				I inf = inferenceIds_.getValue(infId);
				assert inf != null : infId;
				return Collections.singleton(inf);
			}
		};
	}

	public int getDerivingInferenceOf(int cId) {
		assert cId != 0 : cId;
		return cId > 0 ? getValue(derivedByPositive_, cId - 1)
				: getValue(derivedByNegative_, -cId - 1);
	}

	public void setIsDerivedBy(int cId, int infId) {
		assert cId != 0 : cId;
		assert infId == 0 || !isDerivedId(-cId) : cId + ": " + infId;
		LOGGER_.trace("{} derived by {}", cId, infId);
		if (cId > 0) {
			derivedByPositive_ = setValue(derivedByPositive_, cId - 1, infId);
		} else {
			derivedByNegative_ = setValue(derivedByNegative_, -cId - 1, infId);
		}
	}

	public boolean isDerivedId(int cId) {
		return getDerivingInferenceOf(cId) > 0;
	}

	private void pruneChanges() {
		LOGGER_.trace("Prunning axiom changes");
		// prune cancelled additions or deletions
		for (int i = 0; i < toPropagateConclusionsSize_; i++) {
			int axId = toPropagateConclusions_[i];
			if (axId > 0) {
				if (isDerivedId(axId)) {
					// addition that was not deleted
					toAddAxioms_ = setValue(toAddAxioms_, toAddAxiomsSize_++,
							axId);
				} else {
					// addition that was deleted; temporary set derivable
					// so that the subsequent (canceling) deletion is ignored
					setIsDerivedBy(axId, toldInferenceId_);
				}
			} else {
				// deletion
				axId = -axId;
				if (!isDerivedId(axId)) {
					// deletion that was not added
					toRemoveAxioms_ = setValue(toRemoveAxioms_,
							toRemoveAxiomsSize_++, axId);
				} else {
					// deletion that was added; temporary set not derivable so
					// that the subsequent (canceling) addition is ignored
					setIsDerivedBy(axId, 0);
				}
			}
		}
		toPropagateConclusionsSize_ = 0;
		// undo additions and deletions so that they are performed by respective
		// addition and deletion phases
		for (int i = 0; i < toAddAxiomsSize_; i++) {
			int axId = toAddAxioms_[i];
			assert isDerivedId(axId) : axId;
			setIsDerivedBy(axId, 0);
		}
		for (int i = 0; i < toRemoveAxiomsSize_; i++) {
			int axId = toRemoveAxioms_[i];
			assert !isDerivedId(axId) : axId;
			setIsDerivedBy(axId, toldInferenceId_);
		}
	}

	private void loadAdditions() {
		LOGGER_.trace("== Loading added axioms ==");
		// schedule additions for propagation
		for (int i = 0; i < toAddAxiomsSize_; i++) {
			int axId = toAddAxioms_[i];
			assert !isDerivedId(axId) : axId;
			setIsDerivedBy(axId, toldInferenceId_);
			int[] infs = getInferencesWithAxiom(axId);
			// fire inferences if necessary
			for (int j = 1; j <= infs[0]; j++) {
				countdown(infs[j]);
			}
		}
		toAddAxiomsSize_ = 0;
	}

	private void loadDeletions() {
		LOGGER_.trace("== Loading removed axioms ==");
		// schedule deletions for propagation
		for (int i = 0; i < toRemoveAxiomsSize_; i++) {
			int axId = toRemoveAxioms_[i];
			assert isDerivedId(axId) : axId;
			setIsDerivedBy(axId, 0);
			int[] infs = getInferencesWithAxiom(axId);
			// fire inferences if necessary
			for (int j = 1; j <= infs[0]; j++) {
				countup(infs[j]);
			}
		}
		toRemoveAxiomsSize_ = 0;
	}

	private boolean isUsed(A axiom) {
		return isDerivedId(axiomIds_.getId(axiom));
	}

	private void propagateAdditions() {
		LOGGER_.trace("== Propagating additions ==");
		while (toPropagateConclusionsSize_ > 0 || toFireInferencesSize_ > 0) {
			for (int i = 0; i < toPropagateConclusionsSize_; i++) {
				int cId = toPropagateConclusions_[i];
				assert cId != 0 : cId;
				LOGGER_.trace("{}: propagating addition", cId);
				int[] infs = cId > 0 ? getInferencesWithPremise(cId)
						: getInferencesWithConclusion(-cId);
				// fire inferences if necessary
				for (int j = 1; j <= infs[0]; j++) {
					countdown(infs[j]);
				}
			}
			toPropagateConclusionsSize_ = 0;
			for (int i = 0; i < toFireInferencesSize_; i++) {
				int infId = toFireInferences_[i];
				if (hasClash()) {
					int rem = getPremisesRemained(infId);
					assert rem <= 1 : rem;
					if (rem > 0) {
						notFire(infId);
					}
					continue;
				}
				LOGGER_.trace("Firing for addition: {}", infId);
				int[] infRec = getList(inferenceRecord_, infId - 1);
				for (int j = 0; j < infRec.length; j++) {
					int cId = infRec[j];
					if (!isDerivedId(-cId)) {
						if (!isDerivedId(cId)) {
							setIsDerivedBy(cId, infId);
							todo(cId);
						}
						break;
					}
				}
			}
			toFireInferencesSize_ = 0;
		}
	}

	private void propagateDeletions() {
		LOGGER_.trace("== Propagating deletions ==");
		int overdeleted = 0;
		while (toPropagateConclusionsSize_ > overdeleted
				|| toFireInferencesSize_ > 0) {
			while (overdeleted < toPropagateConclusionsSize_) {
				int cId = toPropagateConclusions_[overdeleted++];
				assert cId != 0 : cId;
				LOGGER_.trace("{}: propagating deletion", cId);
				int[] infs = cId > 0 ? getInferencesWithPremise(cId)
						: getInferencesWithConclusion(-cId);
				if (infs == null) {
					continue;
				}
				// fire inferences if necessary
				for (int j = 1; j <= infs[0]; j++) {
					countup(infs[j]);
				}
			}
			for (int i = 0; i < toFireInferencesSize_; i++) {
				int infId = toFireInferences_[i];
				LOGGER_.trace("{}: firing for deletion", infId);
				int[] infRec = getList(inferenceRecord_, infId - 1);
				for (int j = 0; j < infRec.length; j++) {
					int cId = infRec[j];
					if (infId == getDerivingInferenceOf(cId)) {
						todo(cId);
						// deriving inference will be cleared later
						break;
					}
				}
			}
			toFireInferencesSize_ = 0;
		}
		// do not clear propagated conclusions, since they may be re-derived
	}

	private void rederive() {
		LOGGER_.trace("== Rederiving ==");
		int toPropagate = toPropagateConclusionsSize_;
		toPropagateConclusionsSize_ = 0;
		mainLoop: for (int i = 0; i < toPropagate; i++) {
			int cId = toPropagateConclusions_[i];
			int infId = findDerivingInference(cId);
			if (infId == 0) {
				setIsDerivedBy(cId, 0); // not derived
				LOGGER_.trace("{}: not re-derived", cId);
				continue;
			}
			// else
			LOGGER_.trace("{}: re-derived by {}", cId, infId);
			setIsDerivedBy(cId, infId);
			todo(cId);
			int[] infRec = getList(inferenceRecord_, infId - 1);
			for (int j = 0; j < infRec.length; j++) {
				if (infRec[j] == cId) {
					continue mainLoop;
				}
			}
			assert false : Arrays.toString(infRec);
		}
		int unfired = unfiredInferencesSize_;
		unfiredInferencesSize_ = 0;
		for (int i = 0; i < unfired; i++) {
			int infId = unfiredInferences_[i];
			if (infId == toldInferenceId_) {
				// clash due to query will be checked
				continue;
			}
			LOGGER_.trace("Checking to fire: {}", infId);
			int rem = getPremisesRemained(infId);
			if (rem <= 1) {
				if (rem == 1 && !hasClash()) {
					toFire(infId);
				} else {
					notFire(infId);
				}
			}
		}
	}

	int findDerivingInference(int cId) {
		if (isDerivedId(-cId)) {
			// could not be propagated by another inference
			return 0;
		}
		int[] infs = cId > 0 ? getInferencesWithConclusion(cId)
				: getInferencesWithPremise(-cId);
		for (int j = 1; j <= infs[0]; j++) {
			int infId = infs[j];
			if (getPremisesRemained(infId) == 1) {
				return infId;
			}
		}
		return 0;
	}

	private void countdown(int infId) {
		LOGGER_.trace("Countdown inference {}", infId);
		int rem = getPremisesRemained(infId);
		assert rem > 0 : rem;
		rem--;
		if (rem <= 1) {
			if (hasClash()) {
				notFire(infId);
			} else if (rem == 0) {
				LOGGER_.trace("Clash by inference: {}", infId);
				notFire(infId);
			} else { // if rem == 1
				toFire(infId);
			}
		}
		setPremisesRemained(infId, rem);
	}

	private void countup(int infId) {
		LOGGER_.trace("Countup inference {}", infId);
		int rem = getPremisesRemained(infId);
		if (rem <= 1) {
			toFire(infId);
		}
		rem++;
		setPremisesRemained(infId, rem);
	}

	private void notFire(int infId) {
		LOGGER_.trace("{}: not firing due to clash", infId);
		unfiredInferences_ = setValue(unfiredInferences_,
				unfiredInferencesSize_++, infId);
	}

	private void toFire(int infId) {
		LOGGER_.trace("{}: to fire", infId);
		toFireInferences_ = setValue(toFireInferences_, toFireInferencesSize_++,
				infId);
	}

	private void todo(int cId) {
		assert cId != 0 : cId;
		toPropagateConclusions_ = setValue(toPropagateConclusions_,
				toPropagateConclusionsSize_++, cId);
	}

	private boolean hasClash() {
		return unfiredInferencesSize_ > 0;
	}

	private int getPremisesRemained(int infId) {
		int remained = getValue(inferenceRemainToClash_, infId - 1);
		LOGGER_.trace("Inference {} current premises remained: {}", infId,
				remained);
		return remained;
	}

	private void setPremisesRemained(int infId, int value) {
		LOGGER_.trace("Inference {} remain to fire: {}", infId, value);
		inferenceRemainToClash_ = setValue(inferenceRemainToClash_, infId - 1,
				value);
	}

	private int[] getInferencesWithAxiom(int cId) {
		return getList(inferencesByAxiom_, cId - 1);
	}

	private int[] getInferencesWithPremise(int cId) {
		return getList(inferencesByPremise_, cId - 1);
	}

	private int[] getInferencesWithConclusion(int cId) {
		return getList(inferencesByConclusion_, cId - 1);
	}

	private static int getValue(int[] array, int pos) {
		assert pos >= 0 : pos;
		return pos < array.length ? array[pos] : 0;
	}

	private static final int[] EMPTY_LIST = { 0 };

	private static int[] getList(int[][] array, int pos) {
		assert pos >= 0 : pos;
		int[] result = pos < array.length ? array[pos] : EMPTY_LIST;
		return result == null ? EMPTY_LIST : result;
	}

	private static int[] setValue(int[] array, int pos, int value) {
		assert pos >= 0 : pos;
		while (pos >= array.length) {
			array = resize(array);
		}
		array[pos] = value;
		return array;
	}

	private static int[][] setValue(int[][] array, int pos, int[] value) {
		assert pos >= 0 : pos;
		while (pos >= array.length) {
			array = resize(array);
		}
		array[pos] = value;
		return array;
	}

	private static int[][] addValue(int[][] table, int pos, int value,
			int sizePos) {
		assert pos >= 0 : pos;
		while (pos >= table.length) {
			table = resize(table);
		}
		int[] values = table[pos];
		if (values == null) {
			values = new int[sizePos > 8 ? sizePos : 8];
			table[pos] = values;
			values[sizePos] = sizePos;
		}
		int size = ++values[sizePos];
		if (size == values.length) {
			values = resize(values);
			table[pos] = values;
		}
		values[size] = value;
		return table;
	}

	private static int[][] addValue(int[][] table, int pos, int value) {
		return addValue(table, pos, value, 0);
	}

	private static int[] resize(int[] values) {
		return Arrays.copyOf(values, 2 * values.length);
	}

	private static int[][] resize(int[][] values) {
		return Arrays.copyOf(values, 2 * values.length);
	}

}
