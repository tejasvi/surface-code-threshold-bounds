import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2288 = true := by
  decide +kernel

theorem tot2288 : totK PA10K2 A10K2.t2288 = [0, 0, 509620454389, 1798035738712, 1981464438387, 703748657557, 56417823835, 0, 0, 0] := by
  decide +kernel

theorem rows2289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2289 = true := by
  decide +kernel

theorem tot2289 : totK PA10K2 A10K2.t2289 = [0, 0, 288405974479, 1502807750523, 2243327518847, 968668517125, 70386715255, 0, 0, 0] := by
  decide +kernel

theorem rows2290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2290 = true := by
  decide +kernel

theorem tot2290 : totK PA10K2 A10K2.t2290 = [0, 0, 514030322680, 1825852496955, 1900999486339, 660431436332, 64508458883, 0, 0, 0] := by
  decide +kernel

theorem rows2291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2291 = true := by
  decide +kernel

theorem tot2291 : totK PA10K2 A10K2.t2291 = [0, 0, 302107678445, 1461730364043, 2174219560933, 923884602436, 68505636438, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
