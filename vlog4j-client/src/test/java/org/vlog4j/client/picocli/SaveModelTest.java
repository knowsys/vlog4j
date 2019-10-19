package org.vlog4j.client.picocli;

import javax.naming.ConfigurationException;

/*-
 * #%L
 * VLog4j Client
 * %%
 * Copyright (C) 2018 - 2019 VLog4j Developers
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

import org.junit.Assert;

import org.junit.Test;
import org.vlog4j.client.picocli.SaveModel;
import org.vlog4j.client.picocli.SaveQueryResults;

public class SaveModelTest {

	@Test
	public void defaulfConfig() throws ConfigurationException {
		SaveModel sm = new SaveModel();
		sm.setSaveModel(false);
		sm.setOutputModelDirectory("query-results");
		sm.validate();
	}

	@Test
	public void dontSaveEmptyOutput() throws ConfigurationException {
		SaveModel sm = new SaveModel();
		sm.setSaveModel(false);
		sm.setOutputModelDirectory("");
		sm.validate();
	}

	@Test
	public void dontSaveNullOutput() throws ConfigurationException {
		SaveModel sm = new SaveModel();
		sm.setSaveModel(false);
		sm.setOutputModelDirectory(null);
		sm.validate();
	}

	@Test
	public void saveDefaulfDir() throws ConfigurationException {
		SaveModel sm = new SaveModel();
		sm.setSaveModel(true);
		sm.setOutputModelDirectory("query-results");
		sm.validate();
	}

	@Test(expected = ConfigurationException.class)
	public void saveEmptyOutputDir() throws ConfigurationException {
		SaveModel sm = new SaveModel();
		sm.setSaveModel(true);
		sm.setOutputModelDirectory("");
		sm.validate();
	}

	@Test(expected = ConfigurationException.class)
	public void saveNullDir() throws ConfigurationException {
		SaveModel sm = new SaveModel();
		sm.setSaveModel(true);
		sm.setOutputModelDirectory(null);
		sm.validate();
	}
}