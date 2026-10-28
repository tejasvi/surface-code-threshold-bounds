import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6404 = true := by
  decide +kernel

theorem tot6404 : totK PD2M8K2 D2M8K2.t6404 = [0, 189776267916, 461958554292, 234303200884, 16999022416, 0, 0, 0] := by
  decide +kernel

theorem rows6405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6405 = true := by
  decide +kernel

theorem tot6405 : totK PD2M8K2 D2M8K2.t6405 = [0, 55902201273, 346173991577, 414244205612, 79161228214, 1096505104, 0, 0] := by
  decide +kernel

theorem rows6406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6406 = true := by
  decide +kernel

theorem tot6406 : totK PD2M8K2 D2M8K2.t6406 = [0, 0, 269542959629, 502039439375, 124404471283, 3884009855, 0, 0] := by
  decide +kernel

theorem rows6407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6407 = true := by
  decide +kernel

theorem tot6407 : totK PD2M8K2 D2M8K2.t6407 = [0, 0, 197675460980, 475015480532, 186499698833, 9740140984, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
