import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15096 = true := by
  decide +kernel

theorem tot15096 : totK PD2M8K2 D2M8K2.t15096 = [0, 0, 180592786640, 444797531373, 212205961256, 16861767938, 0, 0] := by
  decide +kernel

theorem rows15097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15097 = true := by
  decide +kernel

theorem tot15097 : totK PD2M8K2 D2M8K2.t15097 = [0, 0, 161051593493, 493788190390, 233172762725, 6583237743, 0, 0] := by
  decide +kernel

theorem rows15098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15098 = true := by
  decide +kernel

theorem tot15098 : totK PD2M8K2 D2M8K2.t15098 = [0, 0, 180333937563, 462227372829, 233006585207, 12264129317, 0, 0] := by
  decide +kernel

theorem rows15099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15099 = true := by
  decide +kernel

theorem tot15099 : totK PD2M8K2 D2M8K2.t15099 = [0, 108844600523, 325623280395, 317923850993, 141300169679, 13468148062, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
