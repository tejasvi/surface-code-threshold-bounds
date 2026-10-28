import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t876 = true := by
  decide +kernel

theorem tot876 : totK PA10K2 A10K2.t876 = [0, 374058395286, 1640731473451, 2114280511951, 797369127325, 60390699439, 0, 0, 0, 0] := by
  decide +kernel

theorem rows877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t877 = true := by
  decide +kernel

theorem tot877 : totK PA10K2 A10K2.t877 = [0, 592581714966, 1903474134247, 1885329704741, 537298271406, 31953252077, 0, 0, 0, 0] := by
  decide +kernel

theorem rows878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t878 = true := by
  decide +kernel

theorem tot878 : totK PA10K2 A10K2.t878 = [296996980728, 1026652478477, 1560514591176, 1394354169805, 559910211129, 50555834002, 0, 0, 0, 0] := by
  decide +kernel

theorem rows879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t879 = true := by
  decide +kernel

theorem tot879 : totK PA10K2 A10K2.t879 = [469130319405, 1764085250098, 2053063811515, 739797908533, 43692506903, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
