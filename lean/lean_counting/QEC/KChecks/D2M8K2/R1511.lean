import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6044 = true := by
  decide +kernel

theorem tot6044 : totK PD2M8K2 D2M8K2.t6044 = [0, 0, 222677394873, 496605824089, 168628487050, 5008494805, 0, 0] := by
  decide +kernel

theorem rows6045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6045 = true := by
  decide +kernel

theorem tot6045 : totK PD2M8K2 D2M8K2.t6045 = [0, 0, 177545542208, 449624416044, 253098765339, 27717970206, 0, 0] := by
  decide +kernel

theorem rows6046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6046 = true := by
  decide +kernel

theorem tot6046 : totK PD2M8K2 D2M8K2.t6046 = [0, 0, 185780873423, 452318524694, 251709595271, 16466788057, 0, 0] := by
  decide +kernel

theorem rows6047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6047 = true := by
  decide +kernel

theorem tot6047 : totK PD2M8K2 D2M8K2.t6047 = [0, 0, 190694887764, 466956726003, 223004969884, 11982551986, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
