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
