import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14456 = true := by
  decide +kernel

theorem tot14456 : totK PD2M8K2 D2M8K2.t14456 = [124038552898, 321580893705, 330856736189, 146504632024, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows14457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14457 = true := by
  decide +kernel

theorem tot14457 : totK PD2M8K2 D2M8K2.t14457 = [192406290166, 463826260116, 232974905937, 15118300184, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14458 = true := by
  decide +kernel

theorem tot14458 : totK PD2M8K2 D2M8K2.t14458 = [126175521938, 438148218938, 313462178309, 36297015803, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14459 = true := by
  decide +kernel

theorem tot14459 : totK PD2M8K2 D2M8K2.t14459 = [0, 180797898158, 447971038481, 255978478332, 25373788367, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
