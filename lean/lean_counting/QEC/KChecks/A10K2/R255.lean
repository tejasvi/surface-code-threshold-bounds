import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1020 = true := by
  decide +kernel

theorem tot1020 : totK PA10K2 A10K2.t1020 = [0, 391064209620, 1235263595393, 1546354405980, 1277891725602, 534212548163, 50499610055, 0, 0, 0] := by
  decide +kernel

theorem rows1021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1021 = true := by
  decide +kernel

theorem tot1021 : totK PA10K2 A10K2.t1021 = [0, 201469472462, 1223868478600, 2166020582207, 1224870946737, 202723134940, 12462147902, 0, 0, 0] := by
  decide +kernel

theorem rows1022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1022 = true := by
  decide +kernel

theorem tot1022 : totK PA10K2 A10K2.t1022 = [0, 305238687968, 1315637650992, 1991013449440, 1144618338237, 207058910250, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1023 = true := by
  decide +kernel

theorem tot1023 : totK PA10K2 A10K2.t1023 = [0, 481782272590, 1878931263789, 2073166095947, 592912593053, 25144157885, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
