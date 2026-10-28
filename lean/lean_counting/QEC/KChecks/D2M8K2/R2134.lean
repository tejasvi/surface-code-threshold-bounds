import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8536 = true := by
  decide +kernel

theorem tot8536 : totK PD2M8K2 D2M8K2.t8536 = [161325574683, 381230554423, 261408537931, 104016753458, 6800370819, 0, 0, 0] := by
  decide +kernel

theorem rows8537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8537 = true := by
  decide +kernel

theorem tot8537 : totK PD2M8K2 D2M8K2.t8537 = [178250940236, 461719049986, 246640902250, 15394402876, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8538 = true := by
  decide +kernel

theorem tot8538 : totK PD2M8K2 D2M8K2.t8538 = [87121289351, 344356848369, 379341440473, 83773805129, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows8539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8539 = true := by
  decide +kernel

theorem tot8539 : totK PD2M8K2 D2M8K2.t8539 = [0, 231489611284, 487809653367, 160808069008, 9404247146, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
