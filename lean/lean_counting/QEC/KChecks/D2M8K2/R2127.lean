import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8508 = true := by
  decide +kernel

theorem tot8508 : totK PD2M8K2 D2M8K2.t8508 = [179781219229, 469342288551, 247684355474, 16245039608, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8509 = true := by
  decide +kernel

theorem tot8509 : totK PD2M8K2 D2M8K2.t8509 = [0, 282418633633, 499723228640, 113383699043, 1260002070, 0, 0, 0] := by
  decide +kernel

theorem rows8510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8510 = true := by
  decide +kernel

theorem tot8510 : totK PD2M8K2 D2M8K2.t8510 = [0, 197601816688, 482143595660, 187092731610, 7259283549, 0, 0, 0] := by
  decide +kernel

theorem rows8511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8511 = true := by
  decide +kernel

theorem tot8511 : totK PD2M8K2 D2M8K2.t8511 = [0, 171008444540, 428135120952, 289659313689, 35390411667, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
