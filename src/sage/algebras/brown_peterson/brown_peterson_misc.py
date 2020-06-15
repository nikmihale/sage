
def monomial_to_string(mono, latex=False, generic=False):

    if latex:
        r = "\\text{r}"
    else:
        r = "r"
    
    if mono == () or mono == (0,):
        return "1"
    else:
        string = r + "(" + str(mono[0])
        for n in mono[1:]:
            string = string + "," + str(n)
        string = string + ")"
    return string.strip(" ")