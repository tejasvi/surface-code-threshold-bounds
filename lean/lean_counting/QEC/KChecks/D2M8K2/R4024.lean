import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16096 = true := by
  decide +kernel

theorem tot16096 : totK PD2M8K2 D2M8K2.t16096 = [0, 0, 305217681093, 497327051911, 102078884001, 1163840124, 0, 0] := by
  decide +kernel

theorem rows16097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16097 = true := by
  decide +kernel

theorem tot16097 : totK PD2M8K2 D2M8K2.t16097 = [0, 0, 200436822144, 481934183580, 183339620452, 10459731235, 0, 0] := by
  decide +kernel

theorem rows16098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16098 = true := by
  decide +kernel

theorem tot16098 : totK PD2M8K2 D2M8K2.t16098 = [0, 196903549238, 462402614592, 244252396666, 23379811609, 0, 0, 0] := by
  decide +kernel

theorem rows16099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16099 = true := by
  decide +kernel

theorem tot16099 : totK PD2M8K2 D2M8K2.t16099 = [0, 198636653544, 478833321916, 215453580393, 11372021936, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
