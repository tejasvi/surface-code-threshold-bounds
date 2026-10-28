import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4260 = true := by
  decide +kernel

theorem tot4260 : totK PA10K2 A10K2.t4260 = [0, 333290887458, 1294330115280, 1889488985157, 1056650736680, 165562159548, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows4261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4261 = true := by
  decide +kernel

theorem tot4261 : totK PA10K2 A10K2.t4261 = [0, 469620549425, 1808551688181, 2129559152322, 714952904733, 37184316439, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4262 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4262 = true := by
  decide +kernel

theorem tot4262 : totK PA10K2 A10K2.t4262 = [0, 0, 590744192387, 2021593185180, 1997150693228, 480184130289, 13229391832, 0, 0, 0] := by
  decide +kernel

theorem rows4263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4263 = true := by
  decide +kernel

theorem tot4263 : totK PA10K2 A10K2.t4263 = [0, 0, 523073057080, 1868547787921, 1934117030990, 596267485786, 49122424979, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
