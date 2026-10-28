import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6656 = true := by
  decide +kernel

theorem tot6656 : totK PD2M8K2 D2M8K2.t6656 = [0, 84985341920, 393848477594, 389177095513, 57377938013, 0, 0, 0] := by
  decide +kernel

theorem rows6657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6657 = true := by
  decide +kernel

theorem tot6657 : totK PD2M8K2 D2M8K2.t6657 = [0, 0, 161426258558, 493277395115, 219755834029, 7416854702, 0, 0] := by
  decide +kernel

theorem rows6658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6658 = true := by
  decide +kernel

theorem tot6658 : totK PD2M8K2 D2M8K2.t6658 = [0, 201466298005, 482715513976, 202702343340, 9852138406, 2313687853, 0, 0] := by
  decide +kernel

theorem rows6659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6659 = true := by
  decide +kernel

theorem tot6659 : totK PD2M8K2 D2M8K2.t6659 = [0, 200581894126, 456460017291, 201392537967, 12463786469, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
