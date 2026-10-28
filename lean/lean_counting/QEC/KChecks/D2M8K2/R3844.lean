import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15376 = true := by
  decide +kernel

theorem tot15376 : totK PD2M8K2 D2M8K2.t15376 = [0, 0, 200262047785, 468422485066, 223480369371, 12204164178, 0, 0] := by
  decide +kernel

theorem rows15377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15377 = true := by
  decide +kernel

theorem tot15377 : totK PD2M8K2 D2M8K2.t15377 = [0, 67143456469, 232179874381, 394165821837, 184972868946, 8209931632, 0, 0] := by
  decide +kernel

theorem rows15378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15378 = true := by
  decide +kernel

theorem tot15378 : totK PD2M8K2 D2M8K2.t15378 = [0, 190195745979, 466928293836, 251388906250, 23201883683, 0, 0, 0] := by
  decide +kernel

theorem rows15379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15379 = true := by
  decide +kernel

theorem tot15379 : totK PD2M8K2 D2M8K2.t15379 = [0, 173591236511, 480305273806, 229354992676, 12373752831, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
