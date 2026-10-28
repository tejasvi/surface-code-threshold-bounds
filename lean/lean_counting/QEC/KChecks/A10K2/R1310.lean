import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5240 = true := by
  decide +kernel

theorem tot5240 : totK PA10K2 A10K2.t5240 = [0, 0, 208565205755, 1410861422055, 2158975500832, 819423897630, 60197561511, 0, 0, 0] := by
  decide +kernel

theorem rows5241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5241 = true := by
  decide +kernel

theorem tot5241 : totK PA10K2 A10K2.t5241 = [0, 0, 0, 625909549387, 2090504605075, 1660976197114, 280057845657, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5242 = true := by
  decide +kernel

theorem tot5242 : totK PA10K2 A10K2.t5242 = [0, 0, 0, 483809673960, 1807633328104, 1903493396774, 507930185029, 31756067336, 0, 0] := by
  decide +kernel

theorem rows5243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5243 = true := by
  decide +kernel

theorem tot5243 : totK PA10K2 A10K2.t5243 = [0, 0, 0, 611979622444, 1992037308042, 1702016708099, 373679438418, 13035108529, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
