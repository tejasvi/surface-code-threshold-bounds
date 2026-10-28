import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1460 = true := by
  decide +kernel

theorem tot1460 : totK PA10K2 A10K2.t1460 = [0, 0, 0, 444211917520, 1819601727633, 1923277459349, 477042235959, 31088438951, 0, 0] := by
  decide +kernel

theorem rows1461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1461 = true := by
  decide +kernel

theorem tot1461 : totK PA10K2 A10K2.t1461 = [0, 0, 0, 545063906002, 1961303730957, 1763363815957, 290458392847, 5903815910, 0, 0] := by
  decide +kernel

theorem rows1462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1462 = true := by
  decide +kernel

theorem tot1462 : totK PA10K2 A10K2.t1462 = [0, 0, 0, 0, 800334465816, 2286309244073, 1275384421658, 128908947518, 0, 0] := by
  decide +kernel

theorem rows1463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1463 = true := by
  decide +kernel

theorem tot1463 : totK PA10K2 A10K2.t1463 = [0, 0, 0, 582206494532, 1850579560105, 1677416261508, 550890674474, 112019229096, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
