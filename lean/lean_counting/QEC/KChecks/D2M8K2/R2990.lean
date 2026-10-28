import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11960 = true := by
  decide +kernel

theorem tot11960 : totK PD2M8K2 D2M8K2.t11960 = [0, 193154803119, 472250976159, 219973651155, 12736775215, 0, 0, 0] := by
  decide +kernel

theorem rows11961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11961 = true := by
  decide +kernel

theorem tot11961 : totK PD2M8K2 D2M8K2.t11961 = [0, 165307868664, 449086897408, 275706834526, 27214788375, 0, 0, 0] := by
  decide +kernel

theorem rows11962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11962 = true := by
  decide +kernel

theorem tot11962 : totK PD2M8K2 D2M8K2.t11962 = [0, 153667419549, 451269428701, 266996468123, 17350401355, 0, 0, 0] := by
  decide +kernel

theorem rows11963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11963 = true := by
  decide +kernel

theorem tot11963 : totK PD2M8K2 D2M8K2.t11963 = [0, 0, 226413462555, 482246064602, 164487743491, 7203532459, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
