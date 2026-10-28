import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7868 = true := by
  decide +kernel

theorem tot7868 : totK PA10K2 A10K2.t7868 = [0, 0, 0, 567985811158, 2020404972059, 1976265873056, 404616642748, 12224107035, 0, 0] := by
  decide +kernel

theorem rows7869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7869 = true := by
  decide +kernel

theorem tot7869 : totK PA10K2 A10K2.t7869 = [0, 0, 320479959089, 1149578476039, 1608235703304, 1316564321901, 521903357347, 48886019071, 0, 0] := by
  decide +kernel

theorem rows7870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7870 = true := by
  decide +kernel

theorem tot7870 : totK PA10K2 A10K2.t7870 = [0, 0, 528909646457, 1887814901484, 1887509273102, 475555437560, 12129354050, 0, 0, 0] := by
  decide +kernel

theorem rows7871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7871 = true := by
  decide +kernel

theorem tot7871 : totK PA10K2 A10K2.t7871 = [0, 0, 0, 615224307360, 2029480844861, 1751110284598, 417047799632, 25734533292, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
