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
 * Obtaining fresh integer identifiers starting from 1
 * 
 * @author Yevgeny Kazakov
 *
 */
public class IdSupplier {

	private int lastId_ = 0;

	/**
	 * @return the next fresh integer identifier; it is guaranteed that this
	 *         identifier was not returned by the previous calls of the method
	 */
	public int getNextId() {
		return ++lastId_;
	}

	/**
	 * @return the identifier provided by the last call of {@link #getNextId()}
	 *         or {@code 0} if no identifier was returned so far
	 */
	public int getLastId() {
		return lastId_;
	}

}
