import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7536 = true := by
  decide +kernel

theorem tot7536 : totK PA10K2 A10K2.t7536 = [0, 0, 289345254879, 1491648778684, 2130074138790, 764836575430, 44689285346, 0, 0, 0] := by
  decide +kernel

theorem rows7537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7537 = true := by
  decide +kernel

theorem tot7537 : totK PA10K2 A10K2.t7537 = [0, 0, 199518480860, 1002706006022, 1946414347276, 1309620811634, 206436970244, 6354482628, 0, 0] := by
  decide +kernel

theorem rows7538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7538 = true := by
  decide +kernel

theorem tot7538 : totK PA10K2 A10K2.t7538 = [0, 0, 380185634497, 1680585949236, 2204349574112, 828616179291, 43081863822, 0, 0, 0] := by
  decide +kernel

theorem rows7539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7539 = true := by
  decide +kernel

theorem tot7539 : totK PA10K2 A10K2.t7539 = [0, 0, 172203508332, 965421643927, 2059875982493, 1555618590039, 286765826995, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
