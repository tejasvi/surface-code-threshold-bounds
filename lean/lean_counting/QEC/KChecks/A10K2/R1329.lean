import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5316 = true := by
  decide +kernel

theorem tot5316 : totK PA10K2 A10K2.t5316 = [0, 0, 0, 451885222873, 1797270812400, 1864243114476, 447215510010, 25454126167, 0, 0] := by
  decide +kernel

theorem rows5317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5317 = true := by
  decide +kernel

theorem tot5317 : totK PA10K2 A10K2.t5317 = [0, 0, 0, 0, 804837989135, 2176291378385, 1325358307736, 174073996660, 0, 0] := by
  decide +kernel

theorem rows5318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5318 = true := by
  decide +kernel

theorem tot5318 : totK PA10K2 A10K2.t5318 = [0, 548282633765, 1830884647131, 1678438891799, 420119961539, 52098244366, 156188333899, 91540553519, 6354482628, 0] := by
  decide +kernel

theorem rows5319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5319 = true := by
  decide +kernel

theorem tot5319 : totK PA10K2 A10K2.t5319 = [0, 294540101292, 1458517567029, 2194895358391, 919771232550, 76826318668, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
