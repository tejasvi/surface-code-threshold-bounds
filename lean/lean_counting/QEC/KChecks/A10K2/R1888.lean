import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7552 = true := by
  decide +kernel

theorem tot7552 : totK PA10K2 A10K2.t7552 = [0, 480093498052, 1614271420945, 1507065617657, 390630196387, 254110651313, 419902306845, 136682872893, 6354482628, 0] := by
  decide +kernel

theorem rows7553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7553 = true := by
  decide +kernel

theorem tot7553 : totK PA10K2 A10K2.t7553 = [0, 296516350813, 1528871824970, 2256163870635, 917637570409, 77041900564, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7554 = true := by
  decide +kernel

theorem tot7554 : totK PA10K2 A10K2.t7554 = [0, 111406325205, 698968681822, 1921582272565, 1805113934101, 396990237511, 13364899180, 0, 0, 0] := by
  decide +kernel

theorem rows7555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7555 = true := by
  decide +kernel

theorem tot7555 : totK PA10K2 A10K2.t7555 = [0, 521810078255, 1911234895830, 2072225118474, 599308275979, 36284268064, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
