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

/**
 * A {@link DerivabilityChecker} that can perform checking derivability of
 * conclusions in proofs incrementally after adding or removing axioms. Proofs
 * and derivations returned by {@link DerivabilityChecker#getProof()}
 * {@link DerivabilityChecker#explainIsDerivable(Object)} should reflect only
 * inferences whose all justifications
 * {@link AxiomPinpointingInference#getJustification()} being added and not
 * removed by this {@link IncrementalDerivabilityChecker}.
 *
 * @author Yevgeny Kazakov
 *
 * @param <A>
 *                The type of axioms from inference justifications.
 * @param <I>
 *                The type of inferences
 */
public interface IncrementalDerivabilityChecker<A, I extends AxiomPinpointingInference<?, ? extends A>>
		extends DerivabilityChecker<I> {

	/**
	 * Use the given axiom for derivability checking. Only inferences whose
	 * justifications contain added axioms will be considered for derivability
	 * checking.
	 *
	 * @param axiom
	 *                  the axioms to be added
	 * @return {@code true} if the axiom has been added or {@code false} if the
	 *         axiom was already added before
	 * @see #removeAxiom(Object)
	 */
	public boolean addAxiom(A axiom);

	/**
	 * Do not use the given axiom for derivability checking. Inferences whose
	 * justifications contain this axiom will not be considered for derivability
	 * checking.
	 *
	 * @param axiom
	 *                  an axiom to be removed
	 * @return {@code true} if the axiom has been removed or {@code false} if
	 *         this axiom was not added
	 */
	public boolean removeAxiom(A axiom);

}
