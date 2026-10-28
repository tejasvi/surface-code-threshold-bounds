import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4172 = true := by
  decide +kernel

theorem tot4172 : totK PD2M8K2 D2M8K2.t4172 = [0, 161824035343, 441166249251, 282970573703, 30419930744, 0, 0, 0] := by
  decide +kernel

theorem rows4173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4173 = true := by
  decide +kernel

theorem tot4173 : totK PD2M8K2 D2M8K2.t4173 = [0, 118519189010, 429361475268, 329537410314, 30782291145, 0, 0, 0] := by
  decide +kernel

theorem rows4174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4174 = true := by
  decide +kernel

theorem tot4174 : totK PD2M8K2 D2M8K2.t4174 = [0, 0, 210468550427, 485235615114, 184591716766, 9442382398, 0, 0] := by
  decide +kernel

theorem rows4175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4175 = true := by
  decide +kernel

theorem tot4175 : totK PD2M8K2 D2M8K2.t4175 = [0, 102225942908, 363382850511, 346913092251, 87172285463, 2332816988, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
