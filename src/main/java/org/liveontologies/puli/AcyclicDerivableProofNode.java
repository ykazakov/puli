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

class AcyclicDerivableProofNode<C> extends ConvertedProofNode<C> {

	private final AcyclicDerivableProofNode<C> parent_;

	private final IncrementalDerivabilityChecker<C, AxiomPinpointingInference<ProofNode<C>, C>> checker_;

	AcyclicDerivableProofNode(ProofNode<C> delegate,
			AcyclicDerivableProofNode<C> parent,
			IncrementalDerivabilityChecker<C, AxiomPinpointingInference<ProofNode<C>, C>> checker) {
		super(delegate);
		this.parent_ = parent;
		this.checker_ = checker;
	}

	AcyclicDerivableProofNode(ProofNode<C> delegate,
			Proof<AxiomPinpointingInference<ProofNode<C>, C>> proof) {
		this(delegate, null,
				new DerivabilityCheckerUP<C, AxiomPinpointingInference<ProofNode<C>, C>>(
						proof));
		Proofs.unfoldRecursively(proof, delegate, inf -> {
			checker_.addAxiom(inf.getConclusion().getMember());
			return true;
		});
	}

	AcyclicDerivableProofNode(ProofNode<C> delegate) {
		this(delegate, Proofs.transform(ProofNodes.getProof(delegate),
				step -> new AxiomPinpointingInferenceAdapter<ProofNode<C>, C>(
						step) {
					@Override
					public Set<? extends C> getJustification() {
						return Collections
								.singleton(step.getConclusion().getMember());
					};
				}));
	}

	@Override
	protected void convertInferences() {
		AcyclicDerivableProofNode<C> blocked = this;
		do {
			checker_.removeAxiom(blocked.getMember());
			blocked = blocked.parent_;
		} while (blocked != null);
		super.convertInferences();
		blocked = this;
		do {
			checker_.addAxiom(blocked.getMember());
			blocked = blocked.parent_;
		} while (blocked != null);
	}

	@Override
	protected final void convert(ConvertedProofStep<C> step) {
		ProofStep<C> delegate = step.getDelegate();
		for (ProofNode<C> premise : delegate.getPremises()) {
			if (!checker_.isDerivable(premise)) {
				return;
			}
		}
		// all premises are derivable
		convert(new AcyclicDerivableProofStep<C>(delegate, this, checker_));
	}

	void convert(AcyclicDerivableProofStep<C> step) {
		super.convert(step);
	}

}
