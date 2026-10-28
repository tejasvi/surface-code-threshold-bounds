import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9796 = true := by
  decide +kernel

theorem tot9796 : totK PD2M8K2 D2M8K2.t9796 = [0, 195768945080, 494106438569, 206570718126, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows9797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9797 = true := by
  decide +kernel

theorem tot9797 : totK PD2M8K2 D2M8K2.t9797 = [0, 170676523351, 457563290016, 238754589960, 13792048390, 0, 0, 0] := by
  decide +kernel

theorem rows9798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9798 = true := by
  decide +kernel

theorem tot9798 : totK PD2M8K2 D2M8K2.t9798 = [0, 0, 282516743281, 499469752637, 110561075096, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9799 = true := by
  decide +kernel

theorem tot9799 : totK PD2M8K2 D2M8K2.t9799 = [0, 86934566719, 392645164877, 379512652559, 41765211743, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
