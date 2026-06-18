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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;
import java.util.Collection;
import java.util.Set;

import org.liveontologies.puli.AxiomPinpointingInference;
import org.liveontologies.puli.DerivabilityCheckerUP;
import org.liveontologies.puli.IncrementalDerivabilityChecker;
import org.liveontologies.puli.Proof;
import org.liveontologies.puli.ProofPrinter;
import org.liveontologies.puli.ProofTest;
import org.liveontologies.puli.Proofs;
import org.liveontologies.puli.TestRunner;

public class IncrementalDerivabilityTestRunner<Q, A, I extends AxiomPinpointingInference<?, ? extends A>>
		implements TestRunner<AxiomPinpointingTestManifest<Q, A, I>> {

	@Override
	public String toString() {
		return "CountingDerivabilityChecker";
	}

	@Override
	public String getName() {
		return toString();
	}

	@Override
	public void runTest(AxiomPinpointingTestManifest<Q, A, I> manifest)
			throws IOException {
		Q query = manifest.getInput().getQuery();
		Proof<? extends I> proof = manifest.getInput().getProof(query);
		IncrementalDerivabilityChecker<A, I> checker = new DerivabilityCheckerUP<>(
				proof);
		Collection<? extends Set<? extends A>> justifications = manifest
				.getJustifications();
		if (justifications != null) {
			for (Set<? extends A> justification : justifications) {
				justification.forEach(ax -> add(checker, ax));
				ProofTest.assertDerivable(checker, query,
						justification::contains);
				for (A axiom : justification) {
					assertTrue("Axiom " + axiom + " cannot be removed!",
							checker.removeAxiom(axiom));
					assertFalse("Axiom " + axiom +" cannot be removed two times!",
							checker.removeAxiom(axiom));
					if (checker.isDerivable(query)) {
						fail("Axiom " + axiom
								+ " can be removed from justification "
								+ justification
								+ " without breaking the derivation:\n"
								+ ProofPrinter.toString(
										checker.explainIsDerivable(query), query));

					}
					add(checker, axiom);

				}
				justification.forEach(ax -> remove(checker, ax));
			}
		}
		Collection<? extends Set<? extends A>> repairs = manifest.getRepairs();
		if (repairs != null) {
			Proofs.unfoldRecursively(proof, query, inf -> {
				inf.getJustification().forEach(checker::addAxiom);
				return true;
			});
			for (Set<? extends A> repair : repairs) {
				// System.out.println("Testing repair: " + repair);
				repair.forEach(ax -> remove(checker, ax));
				if (checker.isDerivable(query)) {
					 fail("Repair " + repair + " is invalid for the proof:\n"
					 + ProofPrinter.toString(
					 checker.explainIsDerivable(query), query));
//					fail("Repair " + repair + " is invalid for the proof:\n"
//							+ ProofPrinter.toString(proof, query));
				}
				for (A axiom : repair) {
					checker.addAxiom(axiom);
					if (!checker.isDerivable(query)) {
						fail("Axiom " + axiom + " can be removed from repair "
								+ repair + " keeping non-entailment:\n"
								+ ProofPrinter.toString(proof, query));
					}
					checker.removeAxiom(axiom);
				}
				repair.forEach(ax -> add(checker, ax));

			}

		}
	}

	void remove(IncrementalDerivabilityChecker<A, I> checker, A axiom) {
		checker.removeAxiom(axiom);
		assertFalse("Axiom cannot be removed two times!",
				checker.removeAxiom(axiom));
	}

	void add(IncrementalDerivabilityChecker<A, I> checker, A axiom) {
		checker.addAxiom(axiom);
		assertFalse("Axiom cannot be added two times!",
				checker.addAxiom(axiom));
	}

}
