import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14300 = true := by
  decide +kernel

theorem tot14300 : totK PD2M8K2 D2M8K2.t14300 = [0, 0, 260693877934, 505909965187, 129192228101, 2309606161, 0, 0] := by
  decide +kernel

theorem rows14301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14301 = true := by
  decide +kernel

theorem tot14301 : totK PD2M8K2 D2M8K2.t14301 = [0, 51750414094, 236243557081, 410529161898, 158666934016, 10740121073, 0, 0] := by
  decide +kernel

theorem rows14302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14302 = true := by
  decide +kernel

theorem tot14302 : totK PD2M8K2 D2M8K2.t14302 = [0, 188514029413, 482372715392, 210781129264, 9956742354, 0, 0, 0] := by
  decide +kernel

theorem rows14303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14303 = true := by
  decide +kernel

theorem tot14303 : totK PD2M8K2 D2M8K2.t14303 = [0, 84656827805, 359097606759, 368014599208, 68434060239, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
