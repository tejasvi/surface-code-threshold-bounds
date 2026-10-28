import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1384 = true := by
  decide +kernel

theorem tot1384 : totK PA10K2 A10K2.t1384 = [0, 0, 0, 565569405129, 1920631454815, 1810581225632, 481517781661, 30810868011, 0, 0] := by
  decide +kernel

theorem rows1385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1385 = true := by
  decide +kernel

theorem tot1385 : totK PA10K2 A10K2.t1385 = [0, 0, 477479145708, 1708740314222, 2077601663599, 850154451216, 66327382866, 0, 0, 0] := by
  decide +kernel

theorem rows1386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1386 = true := by
  decide +kernel

theorem tot1386 : totK PA10K2 A10K2.t1386 = [0, 0, 287992640199, 1501372920114, 2252250896046, 989391547912, 113680660229, 0, 0, 0] := by
  decide +kernel

theorem rows1387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1387 = true := by
  decide +kernel

theorem tot1387 : totK PA10K2 A10K2.t1387 = [0, 0, 546243689926, 1887508328030, 1970311562026, 569000794010, 21686146425, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
