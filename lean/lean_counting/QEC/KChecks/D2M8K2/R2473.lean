import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9892 = true := by
  decide +kernel

theorem tot9892 : totK PD2M8K2 D2M8K2.t9892 = [0, 4294967296, 329400099945, 507875406724, 67842268975, 0, 0, 0] := by
  decide +kernel

theorem rows9893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9893 = true := by
  decide +kernel

theorem tot9893 : totK PD2M8K2 D2M8K2.t9893 = [0, 183222865929, 458654456183, 260924100906, 24679749838, 0, 0, 0] := by
  decide +kernel

theorem rows9894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9894 = true := by
  decide +kernel

theorem tot9894 : totK PD2M8K2 D2M8K2.t9894 = [0, 141435500620, 436938998135, 304121183118, 36507218619, 0, 0, 0] := by
  decide +kernel

theorem rows9895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9895 = true := by
  decide +kernel

theorem tot9895 : totK PD2M8K2 D2M8K2.t9895 = [0, 0, 198583915256, 460153579294, 234221392869, 21401067817, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
