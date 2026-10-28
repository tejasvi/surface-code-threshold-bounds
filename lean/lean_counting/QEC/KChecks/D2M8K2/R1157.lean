import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4628 = true := by
  decide +kernel

theorem tot4628 : totK PD2M8K2 D2M8K2.t4628 = [0, 0, 0, 301791978231, 484547257470, 107450227965, 1359761328, 0] := by
  decide +kernel

theorem rows4629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4629 = true := by
  decide +kernel

theorem tot4629 : totK PD2M8K2 D2M8K2.t4629 = [0, 0, 0, 200377199714, 494135773124, 174607257361, 8047123626, 0] := by
  decide +kernel

theorem rows4630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4630 = true := by
  decide +kernel

theorem tot4630 : totK PD2M8K2 D2M8K2.t4630 = [0, 0, 0, 165047014248, 463300495334, 227477597676, 13785089279, 0] := by
  decide +kernel

theorem rows4631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4631 = true := by
  decide +kernel

theorem tot4631 : totK PD2M8K2 D2M8K2.t4631 = [0, 0, 0, 91939516982, 429657608585, 321779910817, 29069209737, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
