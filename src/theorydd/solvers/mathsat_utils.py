MSAT_ENUM_OPTIONS = {
    "model_generation": "false", # force to false so to avoid unnecessary lemmas
    "preprocessor.toplevel_propagation": "false",  # disable non-validity-preserving simplifications
    "preprocessor.simplification": "0",  # same as above
    "dpll.store_tlemmas": "true",  # store T-lemmas
    "theory.la.split_rat_eq": "false",  # avoid generating new atoms for rational equalities
    "theory.bv.eager": "false",  # lazy BV solving (to get lemmas)
    "theory.la.laz_internal_branch_and_bound": "true",  # LIA solving: use internal B&B
    "theory.la.laz_internal_branch_and_bound_limit": "0",
    # "debug.api_call_trace": "3",
}
MSAT_TOTAL_ENUM_OPTIONS = {"dpll.allsat_minimize_model": "false", **MSAT_ENUM_OPTIONS}  # total truth assignments
MSAT_PARTIAL_ENUM_OPTIONS = {"dpll.allsat_minimize_model": "true", **MSAT_ENUM_OPTIONS}  # partial truth assignments


def _allsat_callback_count(models: list[int]):
    """callback for total all-sat"""
    # We cannot pass an int as it would be copied by value, so we
    # use a list with just one element, which is the number of models
    models[0] += 1
    return 1


def _allsat_callback_store(model, converter, models):
    """callback for partial all-sat"""
    py_model = {converter.back(v) for v in model}
    models.append(py_model)
    return 1
