import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11756 = true := by
  decide +kernel

theorem tot11756 : totK PD2M8K2 D2M8K2.t11756 = [0, 0, 225971133628, 501377516969, 155396953093, 2673486229, 0, 0] := by
  decide +kernel

theorem rows11757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11757 = true := by
  decide +kernel

theorem tot11757 : totK PD2M8K2 D2M8K2.t11757 = [0, 0, 199556828850, 484922794569, 175922453390, 9444576055, 0, 0] := by
  decide +kernel

theorem rows11758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11758 = true := by
  decide +kernel

theorem tot11758 : totK PD2M8K2 D2M8K2.t11758 = [0, 0, 215039554237, 481170778955, 177774722327, 5202589208, 0, 0] := by
  decide +kernel

theorem rows11759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11759 = true := by
  decide +kernel

theorem tot11759 : totK PD2M8K2 D2M8K2.t11759 = [0, 38616506213, 206913502559, 434463436908, 202192125315, 12764577078, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
