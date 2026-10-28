import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6224 = true := by
  decide +kernel

theorem tot6224 : totK PD2M8K2 D2M8K2.t6224 = [0, 0, 242658704668, 477112138490, 149356271719, 5706551742, 0, 0] := by
  decide +kernel

theorem rows6225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6225 = true := by
  decide +kernel

theorem tot6225 : totK PD2M8K2 D2M8K2.t6225 = [0, 83524231449, 284796529379, 358879153602, 120507609377, 5853604210, 0, 0] := by
  decide +kernel

theorem rows6226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6226 = true := by
  decide +kernel

theorem tot6226 : totK PD2M8K2 D2M8K2.t6226 = [0, 176309113399, 479531881294, 241830369805, 12206498855, 0, 0, 0] := by
  decide +kernel

theorem rows6227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6227 = true := by
  decide +kernel

theorem tot6227 : totK PD2M8K2 D2M8K2.t6227 = [0, 157300988014, 464595976462, 241192800131, 14812707230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
