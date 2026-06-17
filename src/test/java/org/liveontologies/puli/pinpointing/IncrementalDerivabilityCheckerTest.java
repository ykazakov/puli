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

import org.junit.Before;
import org.junit.Test;
import org.liveontologies.puli.AxiomPinpointingInference;
import org.liveontologies.puli.BaseProofBuilder;
import org.liveontologies.puli.DerivabilityCheckerUP;
import org.liveontologies.puli.IncrementalDerivabilityChecker;
import org.liveontologies.puli.ProofBuilder;

public class IncrementalDerivabilityCheckerTest {

	ProofBuilder<String, Integer, ?> pb;

	IncrementalDerivabilityChecker<Integer, AxiomPinpointingInference<?, Integer>> checker;

	@Before
	public void init() {
		pb = new BaseProofBuilder<>();
		checker = new DerivabilityCheckerUP<>(pb.getProof());
	}

	@Test
	public void testOneRuleTwoAxioms1() {
		pb.conclusion("A").axiom(1).axiom(2).add();
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(1);
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(2);
		assertTrue(checker.isDerivable("A"));
		checker.removeAxiom(1);
		assertFalse(checker.isDerivable("A"));
		checker.removeAxiom(2);
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(1);
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(2);
		assertTrue(checker.isDerivable("A"));
	}

	@Test
	public void testOneRuleTwoAxioms2() {
		pb.conclusion("A").axiom(1).axiom(2).add();
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(1);
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(2);
		assertTrue(checker.isDerivable("A"));
		checker.removeAxiom(1);
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(1);
		assertTrue(checker.isDerivable("A"));
		checker.removeAxiom(2);
		assertFalse(checker.isDerivable("A"));
	}

	@Test
	public void testTwoRulesTwoAxioms() {
		pb.conclusion("A").premise("B").axiom(1).add();
		pb.conclusion("B").axiom(2).add();
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(2);
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(1);
		assertTrue(checker.isDerivable("A"));
		checker.removeAxiom(2);
		assertFalse(checker.isDerivable("A"));
		checker.addAxiom(2);
		assertTrue(checker.isDerivable("A"));
		checker.removeAxiom(1);
		assertFalse(checker.isDerivable("A"));
	}

}
