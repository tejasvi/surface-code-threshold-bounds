import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15048 = true := by
  decide +kernel

theorem tot15048 : totK PD2M8K2 D2M8K2.t15048 = [0, 0, 192513237597, 486999867501, 199099927904, 8669917095, 0, 0] := by
  decide +kernel

theorem rows15049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15049 = true := by
  decide +kernel

theorem tot15049 : totK PD2M8K2 D2M8K2.t15049 = [0, 0, 174279972177, 467119538692, 219587533710, 14631128802, 0, 0] := by
  decide +kernel

theorem rows15050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15050 = true := by
  decide +kernel

theorem tot15050 : totK PD2M8K2 D2M8K2.t15050 = [0, 0, 184856647560, 468482422119, 187960041603, 7799949799, 0, 0] := by
  decide +kernel

theorem rows15051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15051 = true := by
  decide +kernel

theorem tot15051 : totK PD2M8K2 D2M8K2.t15051 = [0, 0, 48253949236, 326717534490, 416506492654, 79540139040, 1288491354, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
