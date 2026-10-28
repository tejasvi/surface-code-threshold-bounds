import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4676 = true := by
  decide +kernel

theorem tot4676 : totK PA10K2 A10K2.t4676 = [0, 0, 968369235466, 2365762823274, 1188646373175, 106742998397, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4677 = true := by
  decide +kernel

theorem tot4677 : totK PA10K2 A10K2.t4677 = [0, 0, 541275038682, 1980597416211, 1759001601048, 366346311868, 11740475125, 0, 0, 0] := by
  decide +kernel

theorem rows4678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4678 = true := by
  decide +kernel

theorem tot4678 : totK PA10K2 A10K2.t4678 = [0, 0, 476086279193, 1771404274145, 1986354556240, 558948100069, 32470938769, 0, 0, 0] := by
  decide +kernel

theorem rows4679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4679 = true := by
  decide +kernel

theorem tot4679 : totK PA10K2 A10K2.t4679 = [0, 0, 531469920453, 1951177350452, 1905963318849, 418142502828, 13227942247, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
