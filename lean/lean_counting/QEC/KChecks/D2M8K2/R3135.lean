import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12540 = true := by
  decide +kernel

theorem tot12540 : totK PD2M8K2 D2M8K2.t12540 = [0, 0, 188203991339, 500216968619, 202069196465, 5430665091, 0, 0] := by
  decide +kernel

theorem rows12541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12541 = true := by
  decide +kernel

theorem tot12541 : totK PD2M8K2 D2M8K2.t12541 = [0, 171270522578, 438190778404, 254736855504, 46933275565, 1187437187, 0, 0] := by
  decide +kernel

theorem rows12542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12542 = true := by
  decide +kernel

theorem tot12542 : totK PD2M8K2 D2M8K2.t12542 = [0, 193705489543, 465559722557, 231247449728, 16430100152, 0, 0, 0] := by
  decide +kernel

theorem rows12543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12543 = true := by
  decide +kernel

theorem tot12543 : totK PD2M8K2 D2M8K2.t12543 = [0, 72707907058, 337832476499, 395315981428, 86387262543, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
