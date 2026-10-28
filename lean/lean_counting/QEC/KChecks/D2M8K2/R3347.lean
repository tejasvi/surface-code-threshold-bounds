import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13388 = true := by
  decide +kernel

theorem tot13388 : totK PD2M8K2 D2M8K2.t13388 = [0, 0, 48477676786, 352404325566, 394651503031, 73682748921, 1095107716, 0] := by
  decide +kernel

theorem rows13389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13389 = true := by
  decide +kernel

theorem tot13389 : totK PD2M8K2 D2M8K2.t13389 = [0, 0, 29720407329, 286154511799, 440083435773, 118532399241, 3882006667, 0] := by
  decide +kernel

theorem rows13390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13390 = true := by
  decide +kernel

theorem tot13390 : totK PD2M8K2 D2M8K2.t13390 = [0, 0, 195709991510, 481624106276, 206096307657, 9852138406, 0, 0] := by
  decide +kernel

theorem rows13391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13391 = true := by
  decide +kernel

theorem tot13391 : totK PD2M8K2 D2M8K2.t13391 = [0, 0, 186541560491, 471466415126, 217416501461, 12534051746, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
