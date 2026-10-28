import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15080 = true := by
  decide +kernel

theorem tot15080 : totK PD2M8K2 D2M8K2.t15080 = [0, 156816874191, 460177135398, 255995304983, 15130787922, 0, 0, 0] := by
  decide +kernel

theorem rows15081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15081 = true := by
  decide +kernel

theorem tot15081 : totK PD2M8K2 D2M8K2.t15081 = [0, 0, 279319074013, 511666006337, 92200473527, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15082 = true := by
  decide +kernel

theorem tot15082 : totK PD2M8K2 D2M8K2.t15082 = [0, 134857906979, 360164422245, 309501161087, 83577534573, 3884009855, 0, 0] := by
  decide +kernel

theorem rows15083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15083 = true := by
  decide +kernel

theorem tot15083 : totK PD2M8K2 D2M8K2.t15083 = [0, 176769099187, 447043495184, 252507045273, 26826777131, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
