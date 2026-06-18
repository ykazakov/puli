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

public class CountingDerivabilityCheckerConclusionRecord<A, I extends AxiomPinpointingInference<?, ? extends A>>
		implements IncrementalDerivabilityChecker<A, I>, Predicate<I> {

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
	// private int[] derivationCount_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * Axiom that can be used for derivations: for each axiom: 1 -used, 0
	 * -unused
	 */
	private int[] usedAxioms_ = new int[INITIAL_ARRY_SIZE_];
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

	public CountingDerivabilityCheckerConclusionRecord(Proof<? extends I> proof) {
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
		int cId = conclusionIds_.getId(inf.getConclusion());
		// System.out.println("Conclusion: " + inf.getConclusion() + " => " +
		// conclusionId);
		List<?> premises = inf.getPremises();
		Set<? extends A> justification = inf.getJustification();
		int rem = premises.size() + justification.size();
		int infId = inferenceIds_.getId(inf);
//		System.out.print("Inference " + infId + ": " + cId + " -|");
		for (A axiom : justification) {
			int axiomId = axiomIds_.getId(axiom);
			inferencesByPremise_ = addValue(inferencesByPremise_, axiomId - 1,
					infId, 1);
			// System.out.println("Axiom: " + axiom + " => " + axiomId);
//			System.out.print(" " + axiomId);
			if (isDerivedId(axiomId)) {
				rem--;
			}
		}
		for (Object premise : premises) {
			int premiseId = conclusionIds_.getId(premise);
			inferencesByPremise_ = addValue(inferencesByPremise_, premiseId - 1,
					infId, 1);
			// System.out.println("Conclusion: " + premise + " => " +
			// premiseId);
//			System.out.print(" " + premiseId);
			if (isDerivedId(premiseId)) {
				rem--;
			}
		}
//		System.out.println();
		conclusionByInference_ = setValue(conclusionByInference_, infId - 1,
				cId);
		inferencesByConclusion_ = addValue(inferencesByConclusion_, cId - 1,
				infId);
		setPremisesRemained(infId, rem);
		if (rem == 0) {
			todo(infId);
			todo(cId);
		}
		return true;
	}

	@Override
	public boolean addAxiom(A axiom) {
		int axId = axiomIds_.getId(axiom);
//		System.out.println("Add: " + axId);
		if (isUsed(axId)) {
//			System.out.println("Ignore");
			return false;
		}
		// else
		setUsed(axId, true);
		todo(axId);
		return true;
	}

	@Override
	public boolean removeAxiom(A axiom) {
		int axId = axiomIds_.getId(axiom);
//		System.out.println("Remove: " + axId);
		if (!isUsed(axId)) {
//			System.out.println("Ignore");
			return false;
		}
		// else
		setUsed(axId, false);
		todo(-axId);
		return true;
	}

	public boolean isDerivedId(int cId) {
		int[] record = getValue(inferencesByPremise_, cId - 1);
		return record != null && record[0] > 0;
	}

	@Override
	public boolean isDerivable(Object conclusion) {
		pruneChanges();
		loadDeletions();
		propagateDeletions();
		rederive();
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
				int[] record = getRecord(cId);
				int infId = record[0];
				if (infId == 0) {
					// not derived
					return Collections.emptySet();
				}
				I inf = inferenceIds_.getValue(infId);
//				System.out.println(inf + " => " + infId);
				return Collections.singleton(inf);
			}
		};
	}

	private void pruneChanges() {
		int pruned = 0;
		while (pruned < todoConclusionsSize_) {
			int axId = todoConclusions_[pruned++];
			if (axId > 0) {
				if (isUsed(axId)) {
					toAddAxioms_ = setValue(toAddAxioms_, toAddAxiomsSize_++,
							axId);
				} else {
//					System.out.println(axId + ": addition cancelled");
					setUsed(axId, true);
				}
			} else {
				axId = -axId;
				if (!isUsed(axId)) {
					toRemoveAxioms_ = setValue(toRemoveAxioms_,
							removedAxiomsSize_++, axId);
				} else {
//					System.out.println(axId + ": deletion cancelled");
					setUsed(axId, false);
				}

			}
		}
		todoConclusionsSize_ = 0;
	}

	private void loadAdditions() {
		int loaded = 0;
		while (loaded < toAddAxiomsSize_) {
			int axId = toAddAxioms_[loaded++];
//			System.out.println(axId + ": load addition");
			todo(1); // told axiom inference
			todo(axId);
		}
		toAddAxiomsSize_ = 0;
	}

	private void loadDeletions() {
		int loaded = 0;
		while (loaded < removedAxiomsSize_) {
			int axId = toRemoveAxioms_[loaded++];
//			System.out.println(axId + ": load deletion");
			todo(1); // told axiom inference
			todo(axId);
		}
		removedAxiomsSize_ = 0;
	}

	// private boolean add(int cId) {
	// // System.out.println("Derived: " + cId + " => " +
	// // conclusionIds_.getValue(cId) + " or "+ axiomIds_.getValue(cId));
	// boolean added = false;
	// int count = getDerivationCount(cId);
	// if (count++ == 0) {
	// todo(cId);
	// added = true;
	// }
	// setDerivationCount(cId, count);
	// return added;
	// }
	//
	// private void delete(int cId, boolean overdelete) {
	// int count = getDerivationCount(cId);
	// assert count > 0;
	// if (--count == 0) {
	// completelyOverDeleted_++;
	// }
	// setDerivationCount(cId, count);
	// if (overdelete) {
	// todo(cId);
	// }
	// }

	private void propagateAdditions() {
		// System.out.println("Propagating additions: " + todoConclusionsSize_);
		int propagated = 0;
		while (propagated < todoConclusionsSize_) {
			int infId = todoConclusions_[propagated++];
			int cId = todoConclusions_[propagated++];
//			System.out.println(
//					"Propagating addition: " + cId + " by inference " + infId);
			addCount_++;
			int[] record = getRecord(cId);
			if (record[0] > 0) {
				// no inferences or already propagated
				continue;
			}
			// record the applied inference
			record[0] = infId;
			// fire inferences if necessary
			for (int i = 2; i <= record[1]; i++) {
				countdown(record[i]);
			}
		}
		todoConclusionsSize_ = 0;
	}

	private void propagateDeletions() {
		// System.out.println("Propagating deletions: " + todoConclusionsSize_);
		int deleted = 0, propagated = 0;
		while (deleted < todoConclusionsSize_) {
			int infId = todoConclusions_[deleted++];
			int cId = todoConclusions_[deleted++];
			overdeleteCount_++;
			int[] record = getRecord(cId);
			if (record[0] != infId) {
				// no inferences or propagated by other inference
				continue;
			}
//			System.out.println(
//					"Propagating deletion: " + cId + " by inference " + infId);
			todoConclusions_[propagated++] = cId;
			// clean applied inference
			record[0] = 0;
			for (int i = 2; i <= record[1]; i++) {
				countup(record[i]);
			}
		}
		todoConclusionsSize_ = propagated;
		// if (completelyOverDeleted_ == todoConclusionsSize_) {
		// // nothing to re-derive
		// todoConclusionsSize_ = 0;
		// }
		// completelyOverDeleted_ = 0;
	}

	private void countdown(int infId) {
		int rem = getPremisesRemained(infId);
//		System.out.println("Countdown inference " + infId + " for " + rem);
		assert rem > 0;
		if (--rem == 0) {
			int cId = conclusionByInference_[infId - 1];
			todo(infId);
			todo(cId);
		}
		setPremisesRemained(infId, rem);
	}

	private void countup(int infId) {
		int rem = getPremisesRemained(infId);
//		System.out.println("Countup inference " + infId + " for " + rem);
		if (rem++ == 0) {
			int cId = conclusionByInference_[infId - 1];
			todo(infId);
			todo(cId);
		}
		setPremisesRemained(infId, rem);
	}

	private void rederive() {
		int overdeleted = 0, rederived = 0;
		while (overdeleted < todoConclusionsSize_) {
			int cId = todoConclusions_[overdeleted++];
			rederiveCheckedCount_++;
			int[] inferences = getValue(inferencesByConclusion_, cId - 1);
			if (inferences == null) {
				continue;
			}
			for (int i = 1; i <= inferences[0]; i++) {
				int infId = inferences[i];
				if (getPremisesRemained(infId) == 0) {
					todoConclusions_[rederived++] = infId;
					todoConclusions_[rederived++] = cId;
//					System.out.println(
//							"Rederiving " + cId + " by inference " + infId);
					break;
				}
			}
		}
		todoConclusionsSize_ = rederived;
	}

	private void todo(int cId) {
		todoConclusions_ = setValue(todoConclusions_, todoConclusionsSize_++,
				cId);
	}

	// private int getDerivationCount(int cId) {
	// return getValue(derivationCount_, cId - 1);
	// }

	// private void setDerivationCount(int cId, int value) {
	// // System.out.println(
	// // cId + " derivations: " + derivationCount_[cId - 1]);
	// derivationCount_ = setValue(derivationCount_, cId - 1, value);
	// }

	private int getPremisesRemained(int infId) {
		int remained = getValue(premisesRemained_, infId - 1);
		// System.out.println(
		// "Inference " + infId + " current premises remained: " + remained);
		return remained;
	}

	private void setPremisesRemained(int infId, int value) {
		// System.out
		// .println("Inference " + infId + " new premises remained: " + value);
		premisesRemained_ = setValue(premisesRemained_, infId - 1, value);
	}

	private boolean isUsed(int axiomId) {
		return getValue(usedAxioms_, axiomId - 1) > 0;
	}

	private void setUsed(int axiomId, boolean isUsed) {
		usedAxioms_ = setValue(usedAxioms_, axiomId - 1, isUsed ? 1 : 0);
	}

	private int[] getRecord(int cId) {
		int[] record = getValue(inferencesByPremise_, cId - 1);
		if (record == null) {
			record = new int[8];
			inferencesByPremise_[cId - 1] = record;
		}
		return record;
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
