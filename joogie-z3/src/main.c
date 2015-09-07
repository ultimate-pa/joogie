/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

#include "main.h"
#include <z3.h>

Z3_context context = NULL;
Z3_model model = NULL;

void myErrorHandler(Z3_context c, Z3_error_code e) {

	Z3_string msg = Z3_get_error_msg(e);

	FILE *f = fopen("C:\\Temp\\errors.txt", "a");
	fprintf(f, "%s\n", msg);
	fclose(f);
}

JNIEXPORT jboolean JNICALL Java_org_joogie_prover_old_Z3ProverEx_createContext(
		JNIEnv * env, jclass clazz) {

	// create config and context
	Z3_config cfg = Z3_mk_config();
	//Z3_set_param_value(cfg, "SOFT_TIMEOUT", "30000");
	context = Z3_mk_context(cfg);
	Z3_del_config(cfg);

	// set error handler
	Z3_set_error_handler(context, myErrorHandler);

	return JNI_TRUE;
}

JNIEXPORT jboolean JNICALL Java_org_joogie_prover_old_Z3ProverEx_deleteContext(
		JNIEnv * env, jclass clazz) {

	// remove context
	Z3_del_context(context);
	context = NULL;

	return JNI_TRUE;
}

JNIEXPORT jboolean JNICALL Java_org_joogie_prover_old_Z3ProverEx_hasContext(
		JNIEnv * env, jclass clazz) {

	return (NULL != context);
}

JNIEXPORT jboolean JNICALL Java_org_joogie_prover_old_Z3ProverEx_push(
		JNIEnv * env, jclass clazz) {

	/*
	 Z3_solver_push(context, solver);
	 if (Z3_OK != Z3_get_error_code(context))
	 return JNI_FALSE;
	 */

	return JNI_TRUE;
}

JNIEXPORT jboolean JNICALL Java_org_joogie_prover_old_Z3ProverEx_pop(
		JNIEnv * env, jclass clazz) {

	/*
	 Z3_solver_pop(context, solver, Z3_solver_get_num_scopes(context, solver));
	 if (Z3_OK != Z3_get_error_code(context))
	 return JNI_FALSE;
	 */

	return JNI_TRUE;
}

JNIEXPORT jint JNICALL Java_org_joogie_prover_old_Z3ProverEx_check(JNIEnv * env,
		jclass clazz, jstring string) {

	Z3_string formula = (*env)->GetStringUTFChars(env, string, NULL);
	Z3_ast ast = Z3_parse_smtlib2_string(context, formula, 0, 0, 0, 0, 0, 0);
	(*env)->ReleaseStringUTFChars(env, string, formula);
	if (Z3_OK != Z3_get_error_code(context))
		return Z3_L_UNDEF;

	Z3_assert_cnstr(context, ast);

	Z3_check_and_get_model(context, &model);

	return (NULL == model) ? Z3_L_FALSE : Z3_L_TRUE;
}

JNIEXPORT jstring JNICALL Java_org_joogie_prover_old_Z3ProverEx_getModel(
		JNIEnv * env, jclass clazz) {

	Z3_string modelAsString = Z3_model_to_string(context, model);
	if (Z3_OK != Z3_get_error_code(context))
		return NULL;

	Z3_del_model(context, model);
	model = NULL;

	return (*env)->NewStringUTF(env, modelAsString);
}
