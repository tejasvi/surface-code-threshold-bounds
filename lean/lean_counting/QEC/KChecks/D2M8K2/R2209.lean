import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8836 = true := by
  decide +kernel

theorem tot8836 : totK PD2M8K2 D2M8K2.t8836 = [192240216830, 474693375397, 223910721639, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8837 = true := by
  decide +kernel

theorem tot8837 : totK PD2M8K2 D2M8K2.t8837 = [69732408475, 327365355279, 406789468287, 92539356919, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8838 = true := by
  decide +kernel

theorem tot8838 : totK PD2M8K2 D2M8K2.t8838 = [32253337614, 337637844545, 480567621688, 63878030079, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8839 = true := by
  decide +kernel

theorem tot8839 : totK PD2M8K2 D2M8K2.t8839 = [202834823356, 472939821742, 199170154943, 9847636232, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
