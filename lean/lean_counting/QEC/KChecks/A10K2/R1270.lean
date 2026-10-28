import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5080 = true := by
  decide +kernel

theorem tot5080 : totK PA10K2 A10K2.t5080 = [0, 0, 535279375809, 1827146175099, 1910676038200, 626754049445, 42079891856, 0, 0, 0] := by
  decide +kernel

theorem rows5081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5081 = true := by
  decide +kernel

theorem tot5081 : totK PA10K2 A10K2.t5081 = [0, 0, 461521015054, 1799808108650, 1958216126390, 535290296165, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows5082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5082 = true := by
  decide +kernel

theorem tot5082 : totK PA10K2 A10K2.t5082 = [0, 0, 107720792190, 930958967400, 2035897456457, 1370192502229, 301846167887, 20331139758, 0, 0] := by
  decide +kernel

theorem rows5083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5083 = true := by
  decide +kernel

theorem tot5083 : totK PA10K2 A10K2.t5083 = [0, 0, 167558341886, 955540132040, 1919030895312, 1323885148495, 255248868387, 10751746851, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
