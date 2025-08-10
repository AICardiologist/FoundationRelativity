# Strip Lean 4 comments with nested /- -/ blocks and -- line comments.
# Prints only code (no comments). Preserves code outside comments on same line.
function strip_line(line,    i, n, out, two) {
  out = ""
  n = length(line); i = 1
  while (i <= n) {
    two = substr(line, i, 2)
    # line comments when not in a block
    if (depth == 0 && two == "--") break
    # open block
    if (two == "/-") { depth++; i += 2; continue }
    # close block
    if (two == "-/" && depth > 0) { depth--; i += 2; continue }
    # normal character: keep only when not in a block
    if (depth == 0) out = out substr(line, i, 1)
    i++
  }
  return out
}
BEGIN { depth = 0 }
{ print strip_line($0) }