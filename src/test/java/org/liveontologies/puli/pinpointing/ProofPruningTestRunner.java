package org.liveontologies.puli.pinpointing;

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

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.Collection;
import java.util.Set;

import org.liveontologies.puli.AxiomPinpointingInference;
import org.liveontologies.puli.Proof;
import org.liveontologies.puli.ProofPrinter;
import org.liveontologies.puli.Proofs;
import org.liveontologies.puli.TestRunner;

public class ProofPruningTestRunner<C, A, I extends AxiomPinpointingInference<? extends C, ? extends A>>
		implements TestRunner<AxiomPinpointingTestManifest<C, A, I>> {

	@Override
	public String toString() {
		return "ProofPruning";
	}

	@Override
	public String getName() {
		return toString();
	}

	@Override
	public void runTest(AxiomPinpointingTestManifest<C, A, I> manifest)
			throws IOException {
		C query = manifest.getInput().getQuery();
		Proof<? extends I> proof = manifest.getInput().getProof(query);
		Proof<? extends I> prunedProof = Proofs.prune(proof, query);
		Collection<? extends Set<? extends A>> justifications = manifest
				.getJustifications();
		if (justifications != null) {
			for (Set<? extends A> justification : justifications) {
				assertTrue(
						"Justification " + justification
								+ " is invalid for the pruned proof:\n"
								+ ProofPrinter.toString(prunedProof, query)
								+ "Original proof:\n"
								+ ProofPrinter.toString(proof, query),
						Proofs.isDerivable(
								Proofs.filter(prunedProof,
										inf -> justification.containsAll(
												inf.getJustification())),
								query));
			}
		}
	}

}
