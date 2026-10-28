import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3384 = true := by
  decide +kernel

theorem tot3384 : totK PA10K2 A10K2.t3384 = [0, 0, 0, 662630700314, 2144567167586, 1813299228359, 312899365963, 6772895877, 0, 0] := by
  decide +kernel

theorem rows3385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3385 = true := by
  decide +kernel

theorem tot3385 : totK PA10K2 A10K2.t3385 = [0, 0, 0, 511300779679, 1771852532042, 1988709459012, 696396300812, 56060786809, 0, 0] := by
  decide +kernel

theorem rows3386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3386 = true := by
  decide +kernel

theorem tot3386 : totK PA10K2 A10K2.t3386 = [0, 0, 0, 440342122742, 1810072946103, 2109872822898, 725574047791, 58106112878, 0, 0] := by
  decide +kernel

theorem rows3387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3387 = true := by
  decide +kernel

theorem tot3387 : totK PA10K2 A10K2.t3387 = [0, 0, 0, 301533737385, 1553267862457, 2140497004201, 894493282919, 72057277339, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
