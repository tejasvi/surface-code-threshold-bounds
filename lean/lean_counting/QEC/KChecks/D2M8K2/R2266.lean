import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9064 = true := by
  decide +kernel

theorem tot9064 : totK PD2M8K2 D2M8K2.t9064 = [0, 90283171180, 228707058234, 353837779670, 198543214954, 15310102822, 0, 0] := by
  decide +kernel

theorem rows9065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9065 = true := by
  decide +kernel

theorem tot9065 : totK PD2M8K2 D2M8K2.t9065 = [0, 154443834110, 477287238089, 241811247926, 12032920807, 0, 0, 0] := by
  decide +kernel

theorem rows9066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9066 = true := by
  decide +kernel

theorem tot9066 : totK PD2M8K2 D2M8K2.t9066 = [0, 170587549806, 454886940175, 246432524686, 14271625646, 0, 0, 0] := by
  decide +kernel

theorem rows9067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9067 = true := by
  decide +kernel

theorem tot9067 : totK PD2M8K2 D2M8K2.t9067 = [0, 0, 282139436832, 503231530587, 99430190900, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
