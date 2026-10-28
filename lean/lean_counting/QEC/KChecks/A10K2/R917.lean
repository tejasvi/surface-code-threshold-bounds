import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3668 = true := by
  decide +kernel

theorem tot3668 : totK PA10K2 A10K2.t3668 = [0, 0, 0, 583410817377, 1996264274707, 1710177555399, 318286296869, 11508786792, 0, 0] := by
  decide +kernel

theorem rows3669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3669 = true := by
  decide +kernel

theorem tot3669 : totK PA10K2 A10K2.t3669 = [0, 0, 0, 476664569020, 1792440063294, 1944064229125, 528579053086, 32356135070, 0, 0] := by
  decide +kernel

theorem rows3670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3670 = true := by
  decide +kernel

theorem tot3670 : totK PA10K2 A10K2.t3670 = [0, 0, 0, 572125365538, 1969624976744, 1830537392499, 363752686372, 12293361420, 0, 0] := by
  decide +kernel

theorem rows3671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3671 = true := by
  decide +kernel

theorem tot3671 : totK PA10K2 A10K2.t3671 = [0, 0, 0, 329443022072, 1640494157598, 2040873352609, 577347254753, 37288523557, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
