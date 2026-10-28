import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4504 = true := by
  decide +kernel

theorem tot4504 : totK PA10K2 A10K2.t4504 = [0, 0, 194171912589, 1081883757897, 1957266931989, 1158841390038, 195181936012, 5453062850, 0, 0] := by
  decide +kernel

theorem rows4505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4505 = true := by
  decide +kernel

theorem tot4505 : totK PA10K2 A10K2.t4505 = [0, 0, 526755891948, 1888993199725, 1799044767994, 437632889000, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows4506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4506 = true := by
  decide +kernel

theorem tot4506 : totK PA10K2 A10K2.t4506 = [0, 0, 0, 817353421571, 2279720109787, 1276390890186, 118569435585, 0, 0, 0] := by
  decide +kernel

theorem rows4507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4507 = true := by
  decide +kernel

theorem tot4507 : totK PA10K2 A10K2.t4507 = [0, 0, 693436352492, 1989453346736, 1658524648366, 498437081344, 95381457924, 5685526223, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
