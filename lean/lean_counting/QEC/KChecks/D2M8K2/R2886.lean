import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11544 = true := by
  decide +kernel

theorem tot11544 : totK PD2M8K2 D2M8K2.t11544 = [0, 0, 239684818222, 488082547138, 151975622716, 4706411597, 0, 0] := by
  decide +kernel

theorem rows11545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11545 = true := by
  decide +kernel

theorem tot11545 : totK PD2M8K2 D2M8K2.t11545 = [0, 0, 186043221075, 459291506208, 236629964703, 26465040141, 0, 0] := by
  decide +kernel

theorem rows11546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11546 = true := by
  decide +kernel

theorem tot11546 : totK PD2M8K2 D2M8K2.t11546 = [0, 0, 170879481649, 444382512428, 264376666905, 16557914790, 0, 0] := by
  decide +kernel

theorem rows11547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11547 = true := by
  decide +kernel

theorem tot11547 : totK PD2M8K2 D2M8K2.t11547 = [0, 0, 160970209301, 460224117879, 267740758026, 14954956764, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
