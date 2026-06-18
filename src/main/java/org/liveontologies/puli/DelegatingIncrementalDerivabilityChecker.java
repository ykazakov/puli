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
 * An {@link IncrementalDerivabilityChecker} that delegates all method calls to
 * the given {@link IncrementalDerivabilityChecker}
 *
 * @author Yevgeny Kazakov
 *
 * @param <A>
 *                The type of axioms from inference justifications.
 * @param <I>
 *                the type of the inference
 * @param <D>
 *                the type of the delegated
 *                {@link DelegatingDerivabilityChecker}
 */
public class DelegatingIncrementalDerivabilityChecker<A, I extends AxiomPinpointingInference<?, ? extends A>, D extends IncrementalDerivabilityChecker<A, I>>
		extends DelegatingDerivabilityChecker<I, D>
		implements IncrementalDerivabilityChecker<A, I> {

	public DelegatingIncrementalDerivabilityChecker(D delegate) {
		super(delegate);
	}

	@Override
	public boolean addAxiom(A axiom) {
		return getDelegate().addAxiom(axiom);
	}

	@Override
	public boolean removeAxiom(A axiom) {
		return getDelegate().removeAxiom(axiom);
	}

}
