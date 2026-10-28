import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11748 = true := by
  decide +kernel

theorem tot11748 : totK PD2M8K2 D2M8K2.t11748 = [0, 0, 208874900997, 485198825308, 175730898789, 7394209392, 0, 0] := by
  decide +kernel

theorem rows11749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11749 = true := by
  decide +kernel

theorem tot11749 : totK PD2M8K2 D2M8K2.t11749 = [0, 0, 188612979234, 468530117058, 214260878734, 14668608167, 0, 0] := by
  decide +kernel

theorem rows11750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11750 = true := by
  decide +kernel

theorem tot11750 : totK PD2M8K2 D2M8K2.t11750 = [0, 0, 213701572426, 478152299266, 155774748966, 4944878611, 0, 0] := by
  decide +kernel

theorem rows11751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11751 = true := by
  decide +kernel

theorem tot11751 : totK PD2M8K2 D2M8K2.t11751 = [0, 0, 19319729168, 317083109406, 423982353890, 81613890576, 1275377855, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
