/- TestKit — the shared test harness (harness, golden, PropSpec, DetSpec,
   DiffSpec, GateKit). -/
import TestKit.Harness
import TestKit.Golden
import TestKit.PropSpec
import TestKit.DetSpec
import TestKit.DiffSpec
import TestKit.GateKit

-- Re-export the LSpec names the repo's Tests actually use so Tests files
-- can import TestKit only (testImportDiscipline: Tests/ must not
-- `import LSpec` — TestKit is the blessed surface).
export LSpec (TestSeq test checkPlausibleIO)
