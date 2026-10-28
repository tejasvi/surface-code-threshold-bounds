import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2320 = true := by
  decide +kernel

theorem tot2320 : totK PA10K2 A10K2.t2320 = [0, 0, 0, 580066233058, 2005589636261, 1807146194384, 358176943159, 12293361420, 0, 0] := by
  decide +kernel

theorem rows2321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2321 = true := by
  decide +kernel

theorem tot2321 : totK PA10K2 A10K2.t2321 = [0, 0, 0, 293916780995, 1560953298523, 2055331978343, 596566702152, 38149021308, 0, 0] := by
  decide +kernel

theorem rows2322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2322 = true := by
  decide +kernel

theorem tot2322 : totK PA10K2 A10K2.t2322 = [0, 0, 276401632319, 697522267209, 871791974299, 1539854615452, 1039009785679, 181660199303, 5982052406, 0] := by
  decide +kernel

theorem rows2323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2323 = true := by
  decide +kernel

theorem tot2323 : totK PA10K2 A10K2.t2323 = [0, 0, 510394552133, 1812289172375, 1935952358683, 733288309194, 65744890498, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
