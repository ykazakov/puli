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

public class CountingDerivabilityCheckerUP<A, I extends AxiomPinpointingInference<?, ? extends A>>
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

	// private int[] conclusionByInference_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * Stores for each inference its conclusion and premises
	 */
	private int[][] inferenceRecord_ = new int[INITIAL_ARRY_SIZE_][];
	/**
	 * Stores for each inference the number of premises to be derived or the
	 * number of goal conclusions to satisfy in order the inference to fire.
	 */
	private int[] inferenceToFire_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * Stores for each conclusion the inference using which it was derived
	 */
	private int[] derivedByPositive_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * Stores for each conclusion the inference using which it was derived
	 */
	private int[] derivedByNegative_ = new int[INITIAL_ARRY_SIZE_];

	/**
	 * The list of axioms pending for addition
	 */
	private int[] toAddAxioms_ = new int[INITIAL_ARRY_SIZE_];
	private int toAddAxiomsSize_ = 0;
	/**
	 * The list of axioms pending for removal
	 */
	private int[] toRemoveAxioms_ = new int[INITIAL_ARRY_SIZE_];
	private int toRemoveAxiomsSize_ = 0;
	/**
	 * Conclusions to be processed
	 */
	private int[] toPropagateConclusions_ = new int[INITIAL_ARRY_SIZE_];
	private int toPropagateConclusionsSize_ = 0;
	/**
	 * Inferences to fire
	 */
	private int[] toFireInferences_ = new int[INITIAL_ARRY_SIZE_];
	private int toFireInferencesSize_ = 0;
	/**
	 * Counts the number of over-deleted conclusions that cannot be re-derived
	 */
	private int completelyOverDeleted_ = 0;

	// statistic
	private int addCount_ = 0, overdeleteCount_ = 0, rederiveCheckedCount_ = 0,
			rederiveRemainCount_ = 0;

	public CountingDerivabilityCheckerUP(Proof<? extends I> proof) {
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

	private int clashCount_ = 0;

	@Override
	public boolean test(I inf) {
		assert toPropagateConclusionsSize_ == 0 : toPropagateConclusionsSize_;
		int cId = conclusionIds_.getId(inf.getConclusion());
		List<?> premises = inf.getPremises();
		Set<? extends A> justification = inf.getJustification();
		int rem = premises.size() + justification.size() + 1;
		int[] infRecord = new int[rem];
		infRecord[0] = cId;
		if (isDerivedId(-cId)) {
			rem--;
		}
		int infId = inferenceIds_.getId(inf);
		int i = 1; // index over infRecord
//		System.out.print("Inference " + infId + ": " + cId + " -|");
		for (A axiom : justification) {
			int axiomId = axiomIds_.getId(axiom);
			inferencesByPremise_ = addValue(inferencesByPremise_, axiomId - 1,
					infId);
			infRecord[i++] = axiomId;
//			System.out.print(" " + axiomId);
			if (isDerivedId(axiomId)) {
				rem--;
			}
		}
		for (Object premise : premises) {
			int premiseId = conclusionIds_.getId(premise);
			inferencesByPremise_ = addValue(inferencesByPremise_, premiseId - 1,
					infId);
			infRecord[i++] = premiseId;
//			System.out.print(" " + premiseId);
			if (isDerivedId(premiseId)) {
				rem--;
			}
		}
//		System.out.println();
		inferencesByConclusion_ = addValue(inferencesByConclusion_, cId - 1,
				infId);
		inferenceRecord_ = setValue(inferenceRecord_, infId - 1, infRecord);
		// conclusionByInference_ = setValue(conclusionByInference_, infId - 1,
		// cId);
		setPremisesRemained(infId, rem);
		if (rem > 1) {
			return true;
		} else if (rem == 1) {
			toFire(infId);
		} else {
			assert rem == 0 : rem;
			clashCount_++;
//			System.out.println("Clash by " + infId);
		}
		return true;
	}

	private static final int TOLD_AXIOM_INFERENCE_ID_ = Integer.MAX_VALUE;

	@Override
	public boolean addAxiom(A axiom) {
		int axId = axiomIds_.getId(axiom);
//		System.out.println("Add: " + axId);
		if (!isDerivedId(axId)) {
			setIsDerivedBy(axId, TOLD_AXIOM_INFERENCE_ID_);
			todo(axId);
			return true;
		} else {
//			System.out.println("Ingored");
			return false;
		}
	}

	@Override
	public boolean removeAxiom(A axiom) {
		int axId = axiomIds_.getId(axiom);
//		System.out.println("Remove: " + axId);
		if (isDerivedId(axId)) {
			setIsDerivedBy(axId, 0);
			todo(-axId);
			return true;
		} else {
//			System.out.println("Ingored");
			return false;
		}
	}

	public int getDerivingInferenceOf(int cId) {
		assert cId != 0 : cId;
		return cId > 0 ? getValue(derivedByPositive_, cId - 1)
				: getValue(derivedByNegative_, -cId - 1);
	}

	public void setIsDerivedBy(int cId, int infId) {
		assert cId != 0 : cId;
//		System.out.println("Set derived " + cId + " by " + infId);
		if (cId > 0) {
			derivedByPositive_ = setValue(derivedByPositive_, cId - 1, infId);
		} else {
			derivedByNegative_ = setValue(derivedByNegative_, -cId - 1, infId);
		}
	}

	public boolean isDerivedId(int cId) {
		return getDerivingInferenceOf(cId) != 0;
	}

	int previousCId = 0;

	@Override
	public boolean isDerivable(Object conclusion) {
		int cId = conclusionIds_.getId(conclusion);
		assert cId != 0 : cId;
		pruneChanges();
		if (cId != previousCId && previousCId != 0) {
			setIsDerivedBy(-previousCId, 0);
			todo(-previousCId);
		}
		loadDeletions();
		propagateDeletions();
		rederive();
		Proofs.unfoldRecursively(proof_, conclusion, this, unfolded_);
		if (cId != previousCId) {
			setIsDerivedBy(-cId, TOLD_AXIOM_INFERENCE_ID_);
			todo(-cId);
		}
		loadAdditions();
		propagateAdditions();
		previousCId = cId;
		boolean result = clashCount_ > 0;
//		System.out.println(
//				conclusionIds_.getId(conclusion) + " derivable: " + result);
		return result;
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
				int[] record = getInferencesWithPremise(cId);
				int infId = record[0];
				if (infId == 0) {
					// not derived
					return Collections.emptySet();
				}
				I inf = inferenceIds_.getValue(infId);
				// System.out.println(inf + " => " + infId);
				return Collections.singleton(inf);
			}
		};
	}

	private void pruneChanges() {
		// prune duplicate or cancelled additions
		for (int i = 0; i < toPropagateConclusionsSize_; i++) {
			int axId = toPropagateConclusions_[i];
			if (axId > 0) {
				// addition, revert
				if (isDerivedId(axId)) {
					toAddAxioms_ = setValue(toAddAxioms_, toAddAxiomsSize_++,
							axId);
				} else {
					setIsDerivedBy(axId, TOLD_AXIOM_INFERENCE_ID_);

				}
			} else {
				// deletion
				axId = -axId;
				if (!isDerivedId(axId)) {
					toRemoveAxioms_ = setValue(toRemoveAxioms_,
							toRemoveAxiomsSize_++, axId);
				} else {
					setIsDerivedBy(axId, 0);
				}
			}
		}
		toPropagateConclusionsSize_ = 0;
		for (int i = 0; i < toAddAxiomsSize_; i++) {
			int axId = toAddAxioms_[i];
			assert isDerivedId(axId) : axId;
			setIsDerivedBy(axId, 0);
		}
		for (int i = 0; i < toRemoveAxiomsSize_; i++) {
			int axId = toRemoveAxioms_[i];
			assert !isDerivedId(axId) : axId;
			setIsDerivedBy(axId, TOLD_AXIOM_INFERENCE_ID_);
		}
	}

	private void loadAdditions() {
		// schedule additions for propagation
		for (int i = 0; i < toAddAxiomsSize_; i++) {
			int axId = toAddAxioms_[i];
			assert !isDerivedId(axId) : axId;
			setIsDerivedBy(axId, TOLD_AXIOM_INFERENCE_ID_);
			todo(axId);
		}
		toAddAxiomsSize_ = 0;
	}

	private void loadDeletions() {
		// schedule deletions for propagation
		for (int i = 0; i < toRemoveAxiomsSize_; i++) {
			int axId = toRemoveAxioms_[i];
			assert isDerivedId(axId) : axId;
			setIsDerivedBy(axId, 0);
			todo(axId);
		}
		toRemoveAxiomsSize_ = 0;
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
		while (toPropagateConclusionsSize_ > 0 || toFireInferencesSize_ > 0) {
			for (int i = 0; i < toPropagateConclusionsSize_; i++) {
				int cId = toPropagateConclusions_[i];
				assert cId != 0 : cId;
				// System.out.println("Propagating addition: " + cId);
				int[] infs = cId > 0 ? getInferencesWithPremise(cId)
						: getInferencesWithConclusion(-cId);
				if (infs == null) {
					continue;
				}
				// fire inferences if necessary
				for (int j = 1; j <= infs[0]; j++) {
					countdown(infs[j]);
				}
			}
			toPropagateConclusionsSize_ = 0;
			for (int i = 0; i < toFireInferencesSize_; i++) {
				int infId = toFireInferences_[i];
//				System.out.println("Firing for addition: " + infId);
				int[] infRec = getValue(inferenceRecord_, infId - 1);
				assert infRec != null : infRec;
				int cId = infRec[0];
				if (!isDerivedId(-cId) && getDerivingInferenceOf(cId) == 0) {
					infRec[0] = -cId; // mark the propagated conclusion
					setIsDerivedBy(cId, infId);
					todo(cId);
					continue;
				}
				for (int j = 1; j < infRec.length; j++) {
					cId = infRec[j];
					if (!isDerivedId(cId)
							&& getDerivingInferenceOf(-cId) == 0) {
						infRec[j] = -cId; // mark the propagated premise
						setIsDerivedBy(-cId, infId);
						todo(-cId);
						break;
					}
				}
			}
			toFireInferencesSize_ = 0;
		}
	}

	private void propagateDeletions() {
		// System.out.println("Propagating deletions: " + todoConclusionsSize_);
		int overdeleted = 0, overfired = 0;
		while (toPropagateConclusionsSize_ - overdeleted > 0
				|| toFireInferencesSize_ - overfired > 0) {
			while (overdeleted < toPropagateConclusionsSize_) {
				int cId = toPropagateConclusions_[overdeleted++];
				assert cId != 0 : cId;
				// System.out.println("Propagating deletion: " + cId);
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
			while (overfired < toFireInferencesSize_) {
				int infId = toFireInferences_[overfired++];
//				System.out.println("Firing for deletion: " + infId);
				int[] infRec = getValue(inferenceRecord_, infId - 1);
				assert infRec != null : infRec;
				int cId = infRec[0];
				if (cId < 0) {
					cId = -cId;
					infRec[0] = cId;
					setIsDerivedBy(cId, 0);
					todo(cId);
					continue;
				}
				for (int j = 1; j < infRec.length; j++) {
					cId = infRec[j];
					if (cId < 0) {
						cId = -cId;
						infRec[j] = cId;
						setIsDerivedBy(-cId, 0);
						todo(-cId);
						break;
					}
				}
			}
		}
	}

	private void rederive() {
		int rederived = 0;
		for (int i = 0; i < toPropagateConclusionsSize_; i++) {
			int cId = toPropagateConclusions_[i];
//			System.out.println("Checking rederivation of " + cId);
			assert !isDerivedId(cId) : cId;
			if (isDerivedId(-cId)) {
				continue;
			}
			int[] infs = cId > 0 ? getInferencesWithConclusion(cId)
					: getInferencesWithPremise(-cId);
			if (infs == null) {
				continue; // cannot be rederived
			}
			for (int j = 1; j <= infs[0]; j++) {
				int infId = infs[j];
				if (getPremisesRemained(infId) == 1) {
//					System.out.println(
//							"Rederiving " + cId + " by inference " + infId);
					setIsDerivedBy(cId, infId);
					toPropagateConclusions_[rederived++] = cId;
					int[] infRec = getValue(inferenceRecord_, infId - 1);
					if (cId > 0) {
						assert infRec[0] == cId : infRec[0];
						infRec[0] = -cId;
					} else {
						cId = -cId;
						for (int k = 1; k < infRec.length; k++) {
							if (infRec[k] == cId) {
								infRec[k] = -cId;
								break;
							}
						}
					}
					break;
				}
			}
		}
		toPropagateConclusionsSize_ = rederived;
		int refired = 0;
		for (int i = 0; i < toFireInferencesSize_; i++) {
			int infId = toFireInferences_[i];
			if (getPremisesRemained(infId) == 1) {
//				System.out.println("Refire: " + infId);
				toFireInferences_[refired++] = infId;
			}
		}
		toFireInferencesSize_ = refired;
	}

	private void countdown(int infId) {
		int rem = getPremisesRemained(infId);
		// System.out.println("Countdown inference " + infId + " for " + rem);
		assert rem > 0 : rem;
		rem--;
		if (rem <= 1) {
			if (rem == 1) {
				toFire(infId);
			} else {
				assert rem == 0 : rem;
				clashCount_++;
//				System.out.println("Clash by " + infId);
			}
		}
		setPremisesRemained(infId, rem);
	}

	private void countup(int infId) {
		int rem = getPremisesRemained(infId);
		// System.out.println("Countup inference " + infId + " for " + rem);
		if (rem <= 1) {
			toFire(infId);
			if (rem == 0) {
				assert rem == 0 : rem;
				clashCount_--;
//				System.out.println("No clash by " + infId);
			}
		}
		rem++;
		setPremisesRemained(infId, rem);
	}

	private void toFire(int infId) {
		toFireInferences_ = setValue(toFireInferences_, toFireInferencesSize_++,
				infId);
	}

	private void todo(int cId) {
		assert cId != 0 : cId;
		toPropagateConclusions_ = setValue(toPropagateConclusions_,
				toPropagateConclusionsSize_++, cId);
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
		int remained = getValue(inferenceToFire_, infId - 1);
		// System.out.println(
		// "Inference " + infId + " current premises remained: " + remained);
		return remained;
	}

	private void setPremisesRemained(int infId, int value) {
		// System.out.println("Inference " + infId + " remain to fire: " +
		// value);
		inferenceToFire_ = setValue(inferenceToFire_, infId - 1, value);
	}

	private int[] getInferencesWithPremise(int cId) {
		return getValue(inferencesByPremise_, cId - 1);
	}

	private int[] getInferencesWithConclusion(int cId) {
		return getValue(inferencesByConclusion_, cId - 1);
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
