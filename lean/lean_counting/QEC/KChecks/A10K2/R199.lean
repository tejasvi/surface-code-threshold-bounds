import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t796 = true := by
  decide +kernel

theorem tot796 : totK PA10K2 A10K2.t796 = [0, 0, 653827800229, 2191442092229, 1830028226184, 333736167486, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t797 = true := by
  decide +kernel

theorem tot797 : totK PA10K2 A10K2.t797 = [134422175332, 329131652317, 520207798212, 1406852413883, 1836321332480, 682726586750, 55515214941, 0, 0, 0] := by
  decide +kernel

theorem rows798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t798 = true := by
  decide +kernel

theorem tot798 : totK PA10K2 A10K2.t798 = [487163420950, 1798686677783, 1925047391655, 559731602273, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t799 = true := by
  decide +kernel

theorem tot799 : totK PA10K2 A10K2.t799 = [225772793739, 1297194143975, 2213361849604, 1186084703609, 127135395881, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
