import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4448 = true := by
  decide +kernel

theorem tot4448 : totK PA10K2 A10K2.t4448 = [0, 0, 328230673014, 1565834216174, 2152978112751, 830254036282, 62685099471, 0, 0, 0] := by
  decide +kernel

theorem rows4449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4449 = true := by
  decide +kernel

theorem tot4449 : totK PA10K2 A10K2.t4449 = [0, 0, 0, 527031195552, 1970768473024, 1971041148381, 404557820602, 12224107035, 0, 0] := by
  decide +kernel

theorem rows4450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4450 = true := by
  decide +kernel

theorem tot4450 : totK PA10K2 A10K2.t4450 = [322245181260, 946639440614, 669932685664, 308751058607, 945795971957, 1242908171025, 512095249310, 48886019071, 0, 0] := by
  decide +kernel

theorem rows4451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4451 = true := by
  decide +kernel

theorem tot4451 : totK PA10K2 A10K2.t4451 = [550059288319, 1833318545110, 1848274223399, 544857809230, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
