import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4924 = true := by
  decide +kernel

theorem tot4924 : totK PA10K2 A10K2.t4924 = [149147014783, 828152689869, 1831687712670, 1636053147241, 429943553423, 31747192500, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4925 = true := by
  decide +kernel

theorem tot4925 : totK PA10K2 A10K2.t4925 = [432946591805, 1830146271155, 2140884471188, 699131256455, 39641288722, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4926 = true := by
  decide +kernel

theorem tot4926 : totK PA10K2 A10K2.t4926 = [0, 594090622979, 2115801044567, 1961877201880, 425158164100, 12855574250, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4927 = true := by
  decide +kernel

theorem tot4927 : totK PA10K2 A10K2.t4927 = [0, 436442116474, 1666673369845, 2010908631701, 774872951480, 69193223626, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
