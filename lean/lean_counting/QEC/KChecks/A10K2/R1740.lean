import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6960 = true := by
  decide +kernel

theorem tot6960 : totK PA10K2 A10K2.t6960 = [0, 0, 557761393270, 1961886021783, 1857616536988, 422084560274, 25533540376, 0, 0, 0] := by
  decide +kernel

theorem rows6961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6961 = true := by
  decide +kernel

theorem tot6961 : totK PA10K2 A10K2.t6961 = [0, 111132462386, 269484551457, 815711437663, 1936258361738, 1239271428331, 202785960908, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6962 = true := by
  decide +kernel

theorem tot6962 : totK PA10K2 A10K2.t6962 = [0, 477584368302, 1837893045921, 2088801029883, 647287765833, 26100353464, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6963 = true := by
  decide +kernel

theorem tot6963 : totK PA10K2 A10K2.t6963 = [0, 75331363467, 758057514199, 2063178872053, 1717537412284, 373724938976, 12462147902, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
