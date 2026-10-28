import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4312 = true := by
  decide +kernel

theorem tot4312 : totK PD2M8K2 D2M8K2.t4312 = [0, 0, 0, 232050444293, 497156298907, 160677221999, 6825433439, 0] := by
  decide +kernel

theorem rows4313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4313 = true := by
  decide +kernel

theorem tot4313 : totK PD2M8K2 D2M8K2.t4313 = [0, 0, 128291511328, 369503332556, 305527230727, 80212133417, 2269197784, 0] := by
  decide +kernel

theorem rows4314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4314 = true := by
  decide +kernel

theorem tot4314 : totK PD2M8K2 D2M8K2.t4314 = [0, 0, 165930123960, 435991968083, 279174258575, 30490141435, 0, 0] := by
  decide +kernel

theorem rows4315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4315 = true := by
  decide +kernel

theorem tot4315 : totK PD2M8K2 D2M8K2.t4315 = [0, 0, 114035045133, 415017526562, 327446250864, 31917054453, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
