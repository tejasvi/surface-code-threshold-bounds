import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8592 = true := by
  decide +kernel

theorem tot8592 : totK PD2M8K2 D2M8K2.t8592 = [0, 90677791058, 373040477590, 349895062507, 57896016893, 1053411165, 0, 0] := by
  decide +kernel

theorem rows8593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8593 = true := by
  decide +kernel

theorem tot8593 : totK PD2M8K2 D2M8K2.t8593 = [0, 18016501081, 276642226496, 453667297446, 102886336245, 3667207281, 0, 0] := by
  decide +kernel

theorem rows8594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8594 = true := by
  decide +kernel

theorem tot8594 : totK PD2M8K2 D2M8K2.t8594 = [0, 181132825682, 460203835580, 244597308801, 20872377286, 0, 0, 0] := by
  decide +kernel

theorem rows8595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8595 = true := by
  decide +kernel

theorem tot8595 : totK PD2M8K2 D2M8K2.t8595 = [0, 208765130498, 473009371947, 213975475151, 12213865680, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
