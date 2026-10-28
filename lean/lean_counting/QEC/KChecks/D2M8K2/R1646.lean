import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6584 = true := by
  decide +kernel

theorem tot6584 : totK PD2M8K2 D2M8K2.t6584 = [166292807903, 443719916446, 275804541916, 30233657518, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6585 = true := by
  decide +kernel

theorem tot6585 : totK PD2M8K2 D2M8K2.t6585 = [120868942948, 435252692551, 317630818310, 24887616287, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6586 = true := by
  decide +kernel

theorem tot6586 : totK PD2M8K2 D2M8K2.t6586 = [0, 210678697539, 486581750604, 181394461213, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows6587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6587 = true := by
  decide +kernel

theorem tot6587 : totK PD2M8K2 D2M8K2.t6587 = [83129224478, 327710499692, 364275210040, 95054212938, 3462014130, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
