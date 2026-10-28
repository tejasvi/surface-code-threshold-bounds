import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1312 = true := by
  decide +kernel

theorem tot1312 : totK PA10K2 A10K2.t1312 = [0, 0, 562168985407, 2017608419622, 1943785824169, 432934473692, 12855574250, 0, 0, 0] := by
  decide +kernel

theorem rows1313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1313 = true := by
  decide +kernel

theorem tot1313 : totK PA10K2 A10K2.t1313 = [0, 0, 474272902674, 1717213840580, 1891874438135, 699584197338, 68750515780, 0, 0, 0] := by
  decide +kernel

theorem rows1314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1314 = true := by
  decide +kernel

theorem tot1314 : totK PA10K2 A10K2.t1314 = [0, 0, 306639967479, 1449366937886, 2151835676693, 941096687562, 76381823220, 0, 0, 0] := by
  decide +kernel

theorem rows1315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1315 = true := by
  decide +kernel

theorem tot1315 : totK PA10K2 A10K2.t1315 = [0, 0, 144290314133, 974526327272, 2062291086059, 1443782338214, 265297957570, 6904928264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
