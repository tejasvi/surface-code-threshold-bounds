import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5168 = true := by
  decide +kernel

theorem tot5168 : totK PA10K2 A10K2.t5168 = [0, 0, 0, 474630013680, 1800385181476, 1747212091784, 450144416918, 31003444686, 0, 0] := by
  decide +kernel

theorem rows5169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5169 = true := by
  decide +kernel

theorem tot5169 : totK PA10K2 A10K2.t5169 = [0, 0, 536528886358, 1847112693286, 1831886874176, 479647019660, 34697220185, 0, 0, 0] := by
  decide +kernel

theorem rows5170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5170 = true := by
  decide +kernel

theorem tot5170 : totK PA10K2 A10K2.t5170 = [0, 0, 308068588377, 1549414368883, 2079302276482, 708963186989, 53117782232, 0, 0, 0] := by
  decide +kernel

theorem rows5171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5171 = true := by
  decide +kernel

theorem tot5171 : totK PA10K2 A10K2.t5171 = [0, 0, 0, 708909143436, 2158159176981, 1509531221690, 253740780393, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
