import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16228 = true := by
  decide +kernel

theorem tot16228 : totK PD2M8K2 D2M8K2.t16228 = [0, 0, 0, 303386893893, 469480325381, 102401484682, 3804183361, 0] := by
  decide +kernel

theorem rows16229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16229 = true := by
  decide +kernel

theorem tot16229 : totK PD2M8K2 D2M8K2.t16229 = [0, 0, 176018543892, 442559788435, 255311070530, 27871274376, 0, 0] := by
  decide +kernel

theorem rows16230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16230 = true := by
  decide +kernel

theorem tot16230 : totK PD2M8K2 D2M8K2.t16230 = [0, 0, 203403748533, 480083990582, 205118097636, 10282528041, 0, 0] := by
  decide +kernel

theorem rows16231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16231 = true := by
  decide +kernel

theorem tot16231 : totK PD2M8K2 D2M8K2.t16231 = [0, 0, 38189920222, 336471538805, 434769127430, 76372873234, 1107157161, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
