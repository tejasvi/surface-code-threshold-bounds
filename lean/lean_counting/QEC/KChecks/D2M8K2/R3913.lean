import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15652 = true := by
  decide +kernel

theorem tot15652 : totK PD2M8K2 D2M8K2.t15652 = [0, 106224090192, 340854405869, 337775329871, 115525400891, 6692597642, 0, 0] := by
  decide +kernel

theorem rows15653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15653 = true := by
  decide +kernel

theorem tot15653 : totK PD2M8K2 D2M8K2.t15653 = [0, 172790466908, 443446366080, 272445056703, 29931978176, 0, 0, 0] := by
  decide +kernel

theorem rows15654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15654 = true := by
  decide +kernel

theorem tot15654 : totK PD2M8K2 D2M8K2.t15654 = [0, 161232167476, 460780277546, 283805980397, 21981409333, 0, 0, 0] := by
  decide +kernel

theorem rows15655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15655 = true := by
  decide +kernel

theorem tot15655 : totK PD2M8K2 D2M8K2.t15655 = [0, 0, 240769877384, 505213769409, 146984631536, 2304167554, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
