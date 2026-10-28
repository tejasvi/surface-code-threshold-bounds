import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3208 = true := by
  decide +kernel

theorem tot3208 : totK PA10K2 A10K2.t3208 = [0, 0, 613779683197, 2043893904628, 1825529263666, 435294556921, 25715051306, 0, 0, 0] := by
  decide +kernel

theorem rows3209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3209 = true := by
  decide +kernel

theorem tot3209 : totK PA10K2 A10K2.t3209 = [0, 334869779639, 1381059998731, 1915873515068, 1058797160961, 185004636031, 6032141194, 0, 0, 0] := by
  decide +kernel

theorem rows3210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3210 = true := by
  decide +kernel

theorem tot3210 : totK PA10K2 A10K2.t3210 = [0, 502001897941, 1876411902129, 2029412141166, 593078802265, 32780473262, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3211 = true := by
  decide +kernel

theorem tot3211 : totK PA10K2 A10K2.t3211 = [0, 0, 633248038475, 2108058431963, 1871070562259, 362567396240, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
