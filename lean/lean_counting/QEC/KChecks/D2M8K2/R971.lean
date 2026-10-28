import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3884 = true := by
  decide +kernel

theorem tot3884 : totK PD2M8K2 D2M8K2.t3884 = [0, 0, 158923014580, 456067150484, 247955896836, 18513104750, 0, 0] := by
  decide +kernel

theorem rows3885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3885 = true := by
  decide +kernel

theorem tot3885 : totK PD2M8K2 D2M8K2.t3885 = [0, 0, 0, 288473961130, 452666970532, 84508520558, 1369150432, 0] := by
  decide +kernel

theorem rows3886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3886 = true := by
  decide +kernel

theorem tot3886 : totK PD2M8K2 D2M8K2.t3886 = [0, 0, 154471804149, 461295918440, 248007768743, 16508110800, 0, 0] := by
  decide +kernel

theorem rows3887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3887 = true := by
  decide +kernel

theorem tot3887 : totK PD2M8K2 D2M8K2.t3887 = [0, 0, 215499957728, 488677731764, 174053451883, 5125504898, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
