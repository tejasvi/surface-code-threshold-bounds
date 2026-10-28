import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11568 = true := by
  decide +kernel

theorem tot11568 : totK PD2M8K2 D2M8K2.t11568 = [68430962919, 335702026847, 395488588845, 80601290310, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows11569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11569 = true := by
  decide +kernel

theorem tot11569 : totK PD2M8K2 D2M8K2.t11569 = [0, 199109705461, 465412021985, 191739962065, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows11570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11570 = true := by
  decide +kernel

theorem tot11570 : totK PD2M8K2 D2M8K2.t11570 = [173447696342, 439161502749, 267893459290, 30984439246, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11571 = true := by
  decide +kernel

theorem tot11571 : totK PD2M8K2 D2M8K2.t11571 = [182931171704, 459854545432, 234089935075, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
