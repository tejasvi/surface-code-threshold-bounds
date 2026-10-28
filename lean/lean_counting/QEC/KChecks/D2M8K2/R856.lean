import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3424 = true := by
  decide +kernel

theorem tot3424 : totK PD2M8K2 D2M8K2.t3424 = [0, 190650412347, 486172828996, 214541104688, 6614204793, 0, 0, 0] := by
  decide +kernel

theorem rows3425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3425 = true := by
  decide +kernel

theorem tot3425 : totK PD2M8K2 D2M8K2.t3425 = [0, 154240658872, 453705991762, 255530843636, 16172581618, 0, 0, 0] := by
  decide +kernel

theorem rows3426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3426 = true := by
  decide +kernel

theorem tot3426 : totK PD2M8K2 D2M8K2.t3426 = [0, 216894327225, 482813069744, 196739560899, 7735362610, 0, 0, 0] := by
  decide +kernel

theorem rows3427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3427 = true := by
  decide +kernel

theorem tot3427 : totK PD2M8K2 D2M8K2.t3427 = [0, 182652924526, 469901056428, 218911888331, 12319708528, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
