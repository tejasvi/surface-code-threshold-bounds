import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1512 = true := by
  decide +kernel

theorem tot1512 : totK PA10K2 A10K2.t1512 = [0, 0, 0, 519063809684, 1959432521208, 1995560267825, 466067494963, 25462924663, 0, 0] := by
  decide +kernel

theorem rows1513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1513 = true := by
  decide +kernel

theorem tot1513 : totK PA10K2 A10K2.t1513 = [0, 0, 0, 0, 796393955886, 2280755009173, 1548977281474, 265800447684, 6904928264, 0] := by
  decide +kernel

theorem rows1514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1514 = true := by
  decide +kernel

theorem tot1514 : totK PA10K2 A10K2.t1514 = [0, 0, 0, 626715473749, 2016297947533, 1885125286111, 612323556256, 42789545874, 0, 0] := by
  decide +kernel

theorem rows1515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1515 = true := by
  decide +kernel

theorem tot1515 : totK PA10K2 A10K2.t1515 = [0, 0, 0, 538649692203, 1933749427692, 1931110208225, 615793951727, 49341381829, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
