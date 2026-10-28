import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14360 = true := by
  decide +kernel

theorem tot14360 : totK PD2M8K2 D2M8K2.t14360 = [0, 190641998706, 459771757355, 250598749818, 18347075350, 0, 0, 0] := by
  decide +kernel

theorem rows14361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14361 = true := by
  decide +kernel

theorem tot14361 : totK PD2M8K2 D2M8K2.t14361 = [0, 59859969972, 329642030830, 413063870803, 89128094884, 1240621948, 0, 0] := by
  decide +kernel

theorem rows14362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14362 = true := by
  decide +kernel

theorem tot14362 : totK PD2M8K2 D2M8K2.t14362 = [0, 0, 266816270113, 494443248899, 136235378914, 3699256714, 0, 0] := by
  decide +kernel

theorem rows14363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14363 = true := by
  decide +kernel

theorem tot14363 : totK PD2M8K2 D2M8K2.t14363 = [0, 0, 201215066267, 486662721649, 191659577363, 10159529672, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
