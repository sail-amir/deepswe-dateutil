"""
Common code used in multiple modules.
"""


def _unfold_rfc_lines(lines):
    i = 0
    while i < len(lines):
        line = lines[i].rstrip()
        if not line:
            del lines[i]
        elif i > 0 and line[0] == " ":
            lines[i-1] += line[1:]
            del lines[i]
        else:
            i += 1

    return lines


class weekday(object):
    __slots__ = ["weekday", "n"]

    def __init__(self, weekday, n=None):
        self.weekday = weekday
        self.n = n

    def __call__(self, n):
        if n == self.n:
            return self
        else:
            return self.__class__(self.weekday, n)

    def __eq__(self, other):
        try:
            if self.weekday != other.weekday or self.n != other.n:
                return False
        except AttributeError:
            return False
        return True

    def __hash__(self):
        return hash((
          self.weekday,
          self.n,
        ))

    def __ne__(self, other):
        return not (self == other)

    def __repr__(self):
        s = ("MO", "TU", "WE", "TH", "FR", "SA", "SU")[self.weekday]
        if not self.n:
            return s
        else:
            return "%s(%+d)" % (s, self.n)

# vim:ts=4:sw=4:et
