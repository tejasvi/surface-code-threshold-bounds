import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6044 = true := by
  decide +kernel

theorem tot6044 : totK PA10K2 A10K2.t6044 = [227315038789, 1177377868658, 2107305700026, 1432927407608, 262321974157, 6851704726, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6045 = true := by
  decide +kernel

theorem tot6045 : totK PA10K2 A10K2.t6045 = [0, 606683590084, 2087978660241, 1955793268812, 440736767253, 12849861599, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6046 = true := by
  decide +kernel

theorem tot6046 : totK PA10K2 A10K2.t6046 = [0, 482498620224, 1705505293183, 1930636535608, 734525781010, 69756018355, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6047 = true := by
  decide +kernel

theorem tot6047 : totK PA10K2 A10K2.t6047 = [0, 296240252308, 1523037562166, 2224606134908, 893501011350, 67798867528, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
