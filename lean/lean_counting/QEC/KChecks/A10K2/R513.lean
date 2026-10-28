import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2052 = true := by
  decide +kernel

theorem tot2052 : totK PA10K2 A10K2.t2052 = [298263154340, 1494319969989, 2044883397052, 719144106144, 53385992088, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2053 = true := by
  decide +kernel

theorem tot2053 : totK PA10K2 A10K2.t2053 = [0, 669790951958, 2113065125814, 1589797613472, 269137921105, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2054 = true := by
  decide +kernel

theorem tot2054 : totK PA10K2 A10K2.t2054 = [0, 560955159923, 1779018487773, 1718859362672, 478799088111, 31987876949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2055 = true := by
  decide +kernel

theorem tot2055 : totK PA10K2 A10K2.t2055 = [0, 439165968624, 1789391683354, 2003903231219, 565105415869, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
