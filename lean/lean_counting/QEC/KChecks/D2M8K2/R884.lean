import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3536 = true := by
  decide +kernel

theorem tot3536 : totK PD2M8K2 D2M8K2.t3536 = [0, 205232224760, 471301347839, 208488207169, 12096313584, 0, 0, 0] := by
  decide +kernel

theorem rows3537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3537 = true := by
  decide +kernel

theorem tot3537 : totK PD2M8K2 D2M8K2.t3537 = [0, 37670822061, 352024796153, 401729524672, 62342033293, 1053411165, 0, 0] := by
  decide +kernel

theorem rows3538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3538 = true := by
  decide +kernel

theorem tot3538 : totK PD2M8K2 D2M8K2.t3538 = [0, 66757013227, 292785015527, 397732826460, 97404982460, 3667207281, 0, 0] := by
  decide +kernel

theorem rows3539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3539 = true := by
  decide +kernel

theorem tot3539 : totK PD2M8K2 D2M8K2.t3539 = [0, 174238557915, 459127052556, 264783009610, 22031215736, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
