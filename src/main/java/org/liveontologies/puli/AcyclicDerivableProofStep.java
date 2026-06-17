/*-
 * #%L
 * Proof Utility Library
 * $Id:$
 * $HeadURL:$
 * %%
 * Copyright (C) 2014 - 2017 Live Ontologies Project
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
package org.liveontologies.puli;

import java.util.Collections;
import java.util.Set;

class AcyclicDerivableProofStep<C> extends ConvertedProofStep<C>
		implements AxiomPinpointingInference<ProofNode<C>, C> {

	private final AcyclicDerivableProofNode<C> conclusion_;

	private final IncrementalDerivabilityChecker<C, AxiomPinpointingInference<ProofNode<C>, C>> checker_;

	AcyclicDerivableProofStep(ProofStep<C> delegate,
			AcyclicDerivableProofNode<C> conclusion,
			IncrementalDerivabilityChecker<C, AxiomPinpointingInference<ProofNode<C>, C>> checker) {
		super(delegate);
		this.conclusion_ = conclusion;
		this.checker_ = checker;
	}

	@Override
	protected AcyclicDerivableProofNode<C> convert(ProofNode<C> premise) {
		return new AcyclicDerivableProofNode<C>(premise, conclusion_, checker_);
	}

	@Override
	public Set<? extends C> getJustification() {
		return Collections.singleton(conclusion_.getDelegate().getMember());
	}

}
