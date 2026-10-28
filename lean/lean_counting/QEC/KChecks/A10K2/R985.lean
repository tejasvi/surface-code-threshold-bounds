import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3940 = true := by
  decide +kernel

theorem tot3940 : totK PA10K2 A10K2.t3940 = [0, 220651030548, 1287647419228, 2283904052235, 1187421821985, 119807857102, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3941 = true := by
  decide +kernel

theorem tot3941 : totK PA10K2 A10K2.t3941 = [0, 74726801304, 587405066834, 1792643434886, 1847688841328, 505052492574, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows3942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3942 = true := by
  decide +kernel

theorem tot3942 : totK PA10K2 A10K2.t3942 = [0, 532233934634, 1850805437377, 1849349308400, 527257221911, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3943 = true := by
  decide +kernel

theorem tot3943 : totK PA10K2 A10K2.t3943 = [0, 135117029674, 1285152490487, 2307244991041, 959386599709, 57767800368, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
