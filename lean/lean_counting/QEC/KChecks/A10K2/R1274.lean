import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5096 = true := by
  decide +kernel

theorem tot5096 : totK PA10K2 A10K2.t5096 = [0, 0, 485525349937, 1845778390439, 1941278805664, 495562975187, 26944146327, 0, 0, 0] := by
  decide +kernel

theorem rows5097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5097 = true := by
  decide +kernel

theorem tot5097 : totK PA10K2 A10K2.t5097 = [0, 0, 515970656656, 1852606306533, 1969618169784, 515181778462, 18754734689, 0, 0, 0] := by
  decide +kernel

theorem rows5098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5098 = true := by
  decide +kernel

theorem tot5098 : totK PA10K2 A10K2.t5098 = [0, 0, 471382281871, 1749057404176, 1848937618783, 506400500702, 44363554315, 0, 0, 0] := by
  decide +kernel

theorem rows5099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5099 = true := by
  decide +kernel

theorem tot5099 : totK PA10K2 A10K2.t5099 = [0, 0, 302082434609, 1522528227729, 2048567193404, 709178042711, 58034192007, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
