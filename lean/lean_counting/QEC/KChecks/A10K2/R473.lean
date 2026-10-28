import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1892 = true := by
  decide +kernel

theorem tot1892 : totK PA10K2 A10K2.t1892 = [0, 118410781347, 241108606521, 427876745845, 1484793868599, 1973022480511, 715766245334, 55515214941, 0, 0] := by
  decide +kernel

theorem rows1893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1893 = true := by
  decide +kernel

theorem tot1893 : totK PA10K2 A10K2.t1893 = [0, 436239151697, 1782534271118, 1970277968446, 523190236326, 26491486257, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1894 = true := by
  decide +kernel

theorem tot1894 : totK PA10K2 A10K2.t1894 = [0, 292708456977, 1396266772403, 2163337128477, 1100606889078, 111502878926, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1895 = true := by
  decide +kernel

theorem tot1895 : totK PA10K2 A10K2.t1895 = [0, 0, 526688570041, 1844697401080, 1845446016837, 489239812130, 31768748853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
