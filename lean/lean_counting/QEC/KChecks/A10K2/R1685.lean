import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6740 = true := by
  decide +kernel

theorem tot6740 : totK PA10K2 A10K2.t6740 = [0, 608105145442, 2016694093706, 1801828327211, 434228176838, 25715051306, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6741 = true := by
  decide +kernel

theorem tot6741 : totK PA10K2 A10K2.t6741 = [322643786975, 1320231252885, 1968457103180, 1111720594882, 186714650158, 6032141194, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6742 = true := by
  decide +kernel

theorem tot6742 : totK PA10K2 A10K2.t6742 = [546006865529, 1947043862300, 1955797860452, 547233962805, 32388916487, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6743 = true := by
  decide +kernel

theorem tot6743 : totK PA10K2 A10K2.t6743 = [0, 765830142136, 2227911347476, 1709694943879, 303703787926, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
