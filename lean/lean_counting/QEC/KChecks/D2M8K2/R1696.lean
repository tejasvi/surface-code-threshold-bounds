import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6784 = true := by
  decide +kernel

theorem tot6784 : totK PD2M8K2 D2M8K2.t6784 = [0, 166849040158, 460227400899, 256699556990, 16111304584, 0, 0, 0] := by
  decide +kernel

theorem rows6785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6785 = true := by
  decide +kernel

theorem tot6785 : totK PD2M8K2 D2M8K2.t6785 = [0, 0, 275233392773, 489144790568, 126138946159, 4009909289, 0, 0] := by
  decide +kernel

theorem rows6786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6786 = true := by
  decide +kernel

theorem tot6786 : totK PD2M8K2 D2M8K2.t6786 = [0, 106467158892, 349396171070, 366325224608, 79271900325, 1149959346, 0, 0] := by
  decide +kernel

theorem rows6787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6787 = true := by
  decide +kernel

theorem tot6787 : totK PD2M8K2 D2M8K2.t6787 = [0, 162498748124, 431587852858, 284322536582, 30329952139, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
