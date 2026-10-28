import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16 = true := by
  decide +kernel

theorem tot16 : totK PD2M8K2 D2M8K2.t16 = [191751915866, 458662133339, 224961502585, 34860472318, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows17 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t17 = true := by
  decide +kernel

theorem tot17 : totK PD2M8K2 D2M8K2.t17 = [189577883613, 460881059103, 234084425534, 17033427234, 0, 0, 0, 0] := by
  decide +kernel

theorem rows18 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t18 = true := by
  decide +kernel

theorem tot18 : totK PD2M8K2 D2M8K2.t18 = [38115386132, 322417732648, 443837761751, 99753463259, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows19 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t19 = true := by
  decide +kernel

theorem tot19 : totK PD2M8K2 D2M8K2.t19 = [0, 203639827644, 479067849102, 185887649370, 7442000727, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
