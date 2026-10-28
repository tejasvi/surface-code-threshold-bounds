import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1464 = true := by
  decide +kernel

theorem tot1464 : totK PA10K2 A10K2.t1464 = [0, 0, 0, 252968100394, 1443278110344, 2215308297450, 841016499400, 61935274286, 0, 0] := by
  decide +kernel

theorem rows1465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1465 = true := by
  decide +kernel

theorem tot1465 : totK PA10K2 A10K2.t1465 = [0, 0, 0, 0, 472280272618, 1836682757504, 1825353557124, 483530250616, 30818366867, 0] := by
  decide +kernel

theorem rows1466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1466 = true := by
  decide +kernel

theorem tot1466 : totK PA10K2 A10K2.t1466 = [0, 0, 0, 464522314952, 1704679102360, 1853443546442, 606854239037, 54854874052, 0, 0] := by
  decide +kernel

theorem rows1467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1467 = true := by
  decide +kernel

theorem tot1467 : totK PA10K2 A10K2.t1467 = [0, 0, 0, 291183364528, 1475203324685, 2110868954739, 741318159477, 45918807480, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
