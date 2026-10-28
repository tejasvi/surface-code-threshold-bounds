import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5300 = true := by
  decide +kernel

theorem tot5300 : totK PA10K2 A10K2.t5300 = [0, 0, 459322409883, 1809094812107, 2042549151227, 622291148861, 25027633033, 0, 0, 0] := by
  decide +kernel

theorem rows5301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5301 = true := by
  decide +kernel

theorem tot5301 : totK PA10K2 A10K2.t5301 = [0, 0, 0, 527544130053, 2003754400101, 1767352390592, 370943081855, 25734533292, 0, 0] := by
  decide +kernel

theorem rows5302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5302 = true := by
  decide +kernel

theorem tot5302 : totK PA10K2 A10K2.t5302 = [0, 0, 481271916829, 1716070335005, 1821286070081, 711939300256, 122048935162, 5718040558, 0, 0] := by
  decide +kernel

theorem rows5303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5303 = true := by
  decide +kernel

theorem tot5303 : totK PA10K2 A10K2.t5303 = [0, 0, 296098192055, 1489150120820, 2136527857911, 786057316251, 52620953014, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
