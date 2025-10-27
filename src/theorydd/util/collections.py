from typing import Callable, Collection, TypeAlias, TypeVar

T = TypeVar('T')
U = TypeVar('U')

Nested: TypeAlias = T | Collection['Nested[T]']


def map_nested(func: Callable[[T], U], data: Nested[T]) -> Nested[U]:
    """Recursively applies a function to leaf elements in a nested collection structure.

    Args:
        func: Function to apply to each leaf element
        data: A leaf element or nested collection of elements

    Returns:
        Transformed structure with same nesting as input
    """
    if isinstance(data, Collection):
        stack = [(False, f) for f in data]
    else:
        stack = [(False, data)]

    output_stack = []

    while stack:
        was_expanded, item = stack.pop()
        if was_expanded:
            if isinstance(item, Collection):
                args = [output_stack.pop() for _ in range(len(item))]
                output_stack.append(type(item)(reversed(args)))
            else:
                output_stack.append(func(item))
        else:
            stack.append((True, item))
            if isinstance(item, Collection):
                for element in item:
                    stack.append((False, element))

    if isinstance(data, Collection):
        return type(data)(reversed([output_stack.pop() for _ in range(len(data))]))
    return output_stack.pop()
