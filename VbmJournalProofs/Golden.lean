import VbmJournal
/-! # The golden file

`tests/golden/slice1.golden` is the text of `VbmJournal.Examples.golden`: the reference executable specification run on the five cases
of the brief (empty journal, one record, torn tail, stale writer, chain tamper) and on a call in flight. This check runs when the
library is built, so a change of the model that changes any trace fails the build until the golden file is regenerated on purpose
(`#eval IO.print VbmJournal.Examples.golden`) and the change reviewed. -/

#guard VbmJournal.Examples.golden == include_str "../tests/golden/slice1.golden"
