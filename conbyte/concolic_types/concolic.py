# Copyright: see copyright.txt

# from abc import ABC

class Concolic: #(ABC):
    @staticmethod
    def _find_engine_in_expr(expr):
        if isinstance(expr, Concolic):
            return expr.engine
        if isinstance(expr, list):
            for e in expr:
                if (engine := Concolic._find_engine_in_expr(e)) is not None:
                    return engine
        return None

# https://stackoverflow.com/questions/16056574/how-does-python-prevent-a-class-from-being-subclassed/16056691#16056691
class MetaFinal(type):
    def __new__(cls, name, bases, classdict):
        for b in bases:
            if isinstance(b, cls):
                raise TypeError(f"type '{b.__name__}' is not an acceptable base type")
        return type.__new__(cls, name, bases, dict(classdict))
