import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2516 = true := by
  decide +kernel

theorem tot2516 : totK PD2M8K2 D2M8K2.t2516 = [93574619190, 384835164297, 394349465357, 51803728907, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2517 = true := by
  decide +kernel

theorem tot2517 : totK PD2M8K2 D2M8K2.t2517 = [162766221026, 456104723560, 279806242951, 22889002939, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2518 = true := by
  decide +kernel

theorem tot2518 : totK PD2M8K2 D2M8K2.t2518 = [174706502236, 466693973831, 247852627126, 13855291977, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2519 = true := by
  decide +kernel

theorem tot2519 : totK PD2M8K2 D2M8K2.t2519 = [0, 180696447629, 441300628994, 262571832037, 25364689049, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
