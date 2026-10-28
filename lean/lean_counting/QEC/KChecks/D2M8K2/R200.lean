import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t800 = true := by
  decide +kernel

theorem tot800 : totK PD2M8K2 D2M8K2.t800 = [0, 54804328219, 387252165511, 408087094247, 51308971623, 0, 0, 0] := by
  decide +kernel

theorem rows801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t801 = true := by
  decide +kernel

theorem tot801 : totK PD2M8K2 D2M8K2.t801 = [0, 67823916352, 310483873062, 405603788164, 108892885548, 3880716147, 0, 0] := by
  decide +kernel

theorem rows802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t802 = true := by
  decide +kernel

theorem tot802 : totK PD2M8K2 D2M8K2.t802 = [0, 158571888790, 445324346378, 282895738929, 28671344309, 0, 0, 0] := by
  decide +kernel

theorem rows803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t803 = true := by
  decide +kernel

theorem tot803 : totK PD2M8K2 D2M8K2.t803 = [0, 179286909697, 467158738021, 248272498995, 14860824504, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
