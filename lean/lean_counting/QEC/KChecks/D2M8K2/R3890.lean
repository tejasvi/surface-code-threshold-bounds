import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15560 = true := by
  decide +kernel

theorem tot15560 : totK PD2M8K2 D2M8K2.t15560 = [0, 0, 170886246066, 469283489537, 231076164884, 13484745446, 0, 0] := by
  decide +kernel

theorem rows15561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15561 = true := by
  decide +kernel

theorem tot15561 : totK PD2M8K2 D2M8K2.t15561 = [0, 0, 0, 316167069553, 507464981257, 82926218958, 0, 0] := by
  decide +kernel

theorem rows15562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15562 = true := by
  decide +kernel

theorem tot15562 : totK PD2M8K2 D2M8K2.t15562 = [0, 0, 89669004421, 289319154890, 383774403951, 122748008012, 5159868635, 0] := by
  decide +kernel

theorem rows15563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15563 = true := by
  decide +kernel

theorem tot15563 : totK PD2M8K2 D2M8K2.t15563 = [0, 0, 156262155296, 459360779254, 284056340210, 29021092090, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
