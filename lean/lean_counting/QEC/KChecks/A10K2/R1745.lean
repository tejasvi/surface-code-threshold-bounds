import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6980 = true := by
  decide +kernel

theorem tot6980 : totK PA10K2 A10K2.t6980 = [0, 0, 0, 624191428874, 2015527095707, 1737444996656, 415772391080, 25734533292, 0, 0] := by
  decide +kernel

theorem rows6981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6981 = true := by
  decide +kernel

theorem tot6981 : totK PA10K2 A10K2.t6981 = [0, 0, 350469507776, 1299798220549, 1785701100421, 1114525829458, 190073027737, 5809256573, 0, 0] := by
  decide +kernel

theorem rows6982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6982 = true := by
  decide +kernel

theorem tot6982 : totK PA10K2 A10K2.t6982 = [0, 0, 234501307853, 1408214279130, 2173971900311, 806577159541, 60214384836, 0, 0, 0] := by
  decide +kernel

theorem rows6983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6983 = true := by
  decide +kernel

theorem tot6983 : totK PA10K2 A10K2.t6983 = [0, 0, 304160910350, 1240978614987, 1965491584826, 1141615006862, 175463850830, 5982052406, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
