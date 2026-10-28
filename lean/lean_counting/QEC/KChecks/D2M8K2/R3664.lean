import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14656 = true := by
  decide +kernel

theorem tot14656 : totK PD2M8K2 D2M8K2.t14656 = [0, 176308135696, 440603533589, 238438065883, 57821066979, 5147854625, 0, 0] := by
  decide +kernel

theorem rows14657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14657 = true := by
  decide +kernel

theorem tot14657 : totK PD2M8K2 D2M8K2.t14657 = [0, 180292384293, 471282829717, 242538910957, 15166893805, 0, 0, 0] := by
  decide +kernel

theorem rows14658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14658 = true := by
  decide +kernel

theorem tot14658 : totK PD2M8K2 D2M8K2.t14658 = [0, 88945508586, 341969862025, 383608717536, 88086797108, 1198073392, 0, 0] := by
  decide +kernel

theorem rows14659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14659 = true := by
  decide +kernel

theorem tot14659 : totK PD2M8K2 D2M8K2.t14659 = [0, 0, 240620204705, 482511162215, 161785632919, 9482920370, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
