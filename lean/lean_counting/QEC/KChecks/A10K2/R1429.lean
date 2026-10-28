import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5716 = true := by
  decide +kernel

theorem tot5716 : totK PA10K2 A10K2.t5716 = [0, 339451561926, 1621925454915, 2038346807401, 698301478151, 56685233921, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5717 = true := by
  decide +kernel

theorem tot5717 : totK PA10K2 A10K2.t5717 = [0, 0, 464111239187, 1842683916414, 1921180379859, 460366766680, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows5718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5718 = true := by
  decide +kernel

theorem tot5718 : totK PA10K2 A10K2.t5718 = [0, 488924837050, 1667504110808, 1766509971515, 734683397924, 124277752561, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5719 = true := by
  decide +kernel

theorem tot5719 : totK PA10K2 A10K2.t5719 = [0, 298064684126, 1550613108317, 2143055878772, 757277322513, 53383554103, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
