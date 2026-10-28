import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11416 = true := by
  decide +kernel

theorem tot11416 : totK PD2M8K2 D2M8K2.t11416 = [0, 0, 157100676091, 443546413167, 282179396052, 28500941422, 0, 0] := by
  decide +kernel

theorem rows11417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11417 = true := by
  decide +kernel

theorem tot11417 : totK PD2M8K2 D2M8K2.t11417 = [0, 0, 103621844536, 427712773676, 322888109111, 26237669221, 0, 0] := by
  decide +kernel

theorem rows11418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11418 = true := by
  decide +kernel

theorem tot11418 : totK PD2M8K2 D2M8K2.t11418 = [0, 0, 0, 217752862651, 499282104153, 144283590036, 3940991112, 0] := by
  decide +kernel

theorem rows11419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11419 = true := by
  decide +kernel

theorem tot11419 : totK PD2M8K2 D2M8K2.t11419 = [0, 0, 154782206337, 434294980945, 284429449059, 36161118250, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
