import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4484 = true := by
  decide +kernel

theorem tot4484 : totK PA10K2 A10K2.t4484 = [281487785300, 1298374235554, 2021159067666, 1179574548704, 218384531759, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4485 = true := by
  decide +kernel

theorem tot4485 : totK PA10K2 A10K2.t4485 = [0, 605532579823, 2067741712527, 1912062265972, 427783457094, 12855574250, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4486 = true := by
  decide +kernel

theorem tot4486 : totK PA10K2 A10K2.t4486 = [0, 279799475968, 1416791576491, 2227760412744, 1084698215799, 105252080563, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4487 = true := by
  decide +kernel

theorem tot4487 : totK PA10K2 A10K2.t4487 = [0, 514966858026, 1797075959726, 1879869610938, 710448620855, 70663383760, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
