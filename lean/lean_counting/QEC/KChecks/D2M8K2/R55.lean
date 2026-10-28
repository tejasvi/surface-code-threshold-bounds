import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t220 = true := by
  decide +kernel

theorem tot220 : totK PD2M8K2 D2M8K2.t220 = [0, 3950786586, 323356793419, 473752356887, 81179204605, 1096505104, 0, 0] := by
  decide +kernel

theorem rows221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t221 = true := by
  decide +kernel

theorem tot221 : totK PD2M8K2 D2M8K2.t221 = [0, 85317676875, 298653167762, 394144025015, 101116978674, 3820764243, 0, 0] := by
  decide +kernel

theorem rows222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t222 = true := by
  decide +kernel

theorem tot222 : totK PD2M8K2 D2M8K2.t222 = [0, 168171533928, 466614960494, 255413863804, 20868494721, 0, 0, 0] := by
  decide +kernel

theorem rows223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t223 = true := by
  decide +kernel

theorem tot223 : totK PD2M8K2 D2M8K2.t223 = [0, 160170732293, 464111030997, 268303122093, 16331735744, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
