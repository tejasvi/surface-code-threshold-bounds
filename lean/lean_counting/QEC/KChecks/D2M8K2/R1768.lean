import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7072 = true := by
  decide +kernel

theorem tot7072 : totK PD2M8K2 D2M8K2.t7072 = [0, 0, 23381866927, 311469305300, 432016868324, 99529840483, 1369150432, 0] := by
  decide +kernel

theorem rows7073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7073 = true := by
  decide +kernel

theorem tot7073 : totK PD2M8K2 D2M8K2.t7073 = [0, 0, 87493257244, 392661884324, 351819540061, 43138632098, 0, 0] := by
  decide +kernel

theorem rows7074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7074 = true := by
  decide +kernel

theorem tot7074 : totK PD2M8K2 D2M8K2.t7074 = [0, 0, 160417751216, 470832620374, 250725866331, 12460012990, 0, 0] := by
  decide +kernel

theorem rows7075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7075 = true := by
  decide +kernel

theorem tot7075 : totK PD2M8K2 D2M8K2.t7075 = [0, 0, 183252185661, 459417015369, 223895017894, 14055478661, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
