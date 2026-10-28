import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3464 = true := by
  decide +kernel

theorem tot3464 : totK PD2M8K2 D2M8K2.t3464 = [0, 162334081073, 442900287644, 279353792656, 30316101566, 0, 0, 0] := by
  decide +kernel

theorem rows3465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3465 = true := by
  decide +kernel

theorem tot3465 : totK PD2M8K2 D2M8K2.t3465 = [0, 116743146825, 445283956278, 308418094460, 17164105546, 0, 0, 0] := by
  decide +kernel

theorem rows3466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3466 = true := by
  decide +kernel

theorem tot3466 : totK PD2M8K2 D2M8K2.t3466 = [0, 0, 327986451727, 515633046945, 73970121098, 0, 0, 0] := by
  decide +kernel

theorem rows3467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3467 = true := by
  decide +kernel

theorem tot3467 : totK PD2M8K2 D2M8K2.t3467 = [0, 174023795246, 377717473938, 296470081293, 79912469016, 1415142070, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
