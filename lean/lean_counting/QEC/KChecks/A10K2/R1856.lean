import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7424 = true := by
  decide +kernel

theorem tot7424 : totK PA10K2 A10K2.t7424 = [0, 0, 0, 551269578005, 1892934245672, 1896636490054, 611421235996, 50403516269, 0, 0] := by
  decide +kernel

theorem rows7425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7425 = true := by
  decide +kernel

theorem tot7425 : totK PA10K2 A10K2.t7425 = [0, 0, 0, 329510379838, 1518729186065, 2175853889605, 875251216181, 62685099471, 0, 0] := by
  decide +kernel

theorem rows7426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7426 = true := by
  decide +kernel

theorem tot7426 : totK PA10K2 A10K2.t7426 = [0, 0, 0, 0, 555528608105, 1981726017790, 1933715738522, 396005587712, 12224107035, 0] := by
  decide +kernel

theorem rows7427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7427 = true := by
  decide +kernel

theorem tot7427 : totK PA10K2 A10K2.t7427 = [0, 322245181260, 977713555127, 723339976121, 295021092637, 894963372464, 1215305555521, 512095249310, 48886019071, 0] := by
  decide +kernel

end QECKChecks.A10K2
