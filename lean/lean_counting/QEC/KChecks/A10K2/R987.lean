import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3948 = true := by
  decide +kernel

theorem tot3948 : totK PA10K2 A10K2.t3948 = [0, 511347151634, 1501006472050, 1341657559689, 775716775832, 569901139456, 132191670027, 6354482628, 0, 0] := by
  decide +kernel

theorem rows3949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3949 = true := by
  decide +kernel

theorem tot3949 : totK PA10K2 A10K2.t3949 = [0, 45274709553, 886979921491, 2179659705597, 1546410975772, 304340221236, 13349922262, 0, 0, 0] := by
  decide +kernel

theorem rows3950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3950 = true := by
  decide +kernel

theorem tot3950 : totK PA10K2 A10K2.t3950 = [0, 464001049335, 1684610951402, 2011929765884, 807061442597, 72263901834, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3951 = true := by
  decide +kernel

theorem tot3951 : totK PA10K2 A10K2.t3951 = [0, 340251942148, 1581397746217, 2139757028326, 887590793326, 78791974533, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
