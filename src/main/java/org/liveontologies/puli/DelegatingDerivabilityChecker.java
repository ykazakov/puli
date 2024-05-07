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
 * A {@link DerivabilityChecker} that delegates all method calls to the given
 * {@link DerivabilityChecker}
 * 
 * @author Yevgeny Kazakov
 *
 * @param <I>
 *                the type of the inference
 * @param <D>
 *                the type of the delegated {@link DerivabilityChecker}
 */
public class DelegatingDerivabilityChecker<I extends Inference<?>, D extends DerivabilityChecker<I>>
		extends Delegator<D> implements DerivabilityChecker<I> {

	public DelegatingDerivabilityChecker(D delegate) {
		super(delegate);
	}

	@Override
	public Proof<? extends I> getProof() {
		return getDelegate().getProof();
	}

	@Override
	public boolean isDerivable(Object conclusion) {
		return getDelegate().isDerivable(conclusion);
	}

	@Override
	public Proof<I> explainIsDerivable(Object conclusion) {
		return getDelegate().explainIsDerivable(conclusion);
	}

}
