import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12904 = true := by
  decide +kernel

theorem tot12904 : totK PD2M8K2 D2M8K2.t12904 = [0, 0, 229346840592, 493561840259, 158847122013, 4927173082, 0, 0] := by
  decide +kernel

theorem rows12905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12905 = true := by
  decide +kernel

theorem tot12905 : totK PD2M8K2 D2M8K2.t12905 = [0, 0, 179305666468, 473229329322, 222634525839, 15967260138, 0, 0] := by
  decide +kernel

theorem rows12906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12906 = true := by
  decide +kernel

theorem tot12906 : totK PD2M8K2 D2M8K2.t12906 = [0, 0, 185196963528, 453110596313, 207491511299, 13603342068, 0, 0] := by
  decide +kernel

theorem rows12907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12907 = true := by
  decide +kernel

theorem tot12907 : totK PD2M8K2 D2M8K2.t12907 = [0, 0, 67052669813, 339232388131, 372804102213, 81369912293, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
