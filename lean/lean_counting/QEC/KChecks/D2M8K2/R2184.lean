import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8736 = true := by
  decide +kernel

theorem tot8736 : totK PD2M8K2 D2M8K2.t8736 = [0, 199455246976, 481215866525, 214286511759, 9943737300, 0, 0, 0] := by
  decide +kernel

theorem rows8737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8737 = true := by
  decide +kernel

theorem tot8737 : totK PD2M8K2 D2M8K2.t8737 = [0, 109668074920, 432098061665, 322604607948, 27900890732, 0, 0, 0] := by
  decide +kernel

theorem rows8738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8738 = true := by
  decide +kernel

theorem tot8738 : totK PD2M8K2 D2M8K2.t8738 = [0, 37952188783, 295244962850, 473493417000, 93434504274, 1310517177, 0, 0] := by
  decide +kernel

theorem rows8739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8739 = true := by
  decide +kernel

theorem tot8739 : totK PD2M8K2 D2M8K2.t8739 = [0, 181395631713, 445920994964, 265662196950, 28324231903, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
